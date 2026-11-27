import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5940_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

abbrev Pool := Finset Nat
def raw : Pool := {15,240,3840,61440,4369,8738,17476,34952,0,65535}
def pos : List Nat := [1,2,3,4,5,8]
def neg : List Nat := [0,6,7,9,10,11,12,13,14,15]

abbrev Separates (S : Pool) := ∀ p ∈ pos, ∀ n ∈ neg,
  ∃ w ∈ S, w.testBit p = true ∧ w.testBit n = false

def combine (op : Bool) (a b : Nat) := if op then a ||| b else a &&& b
def sides (S : Pool) (a b : Nat) : List Pool := [S,(S.erase a),(S.erase b),(S.erase a).erase b]

lemma sides_mem {U : Pool} (a b : Nat) : U ∈ sides (insert a (insert b U)) a b := by
  by_cases ha : a∈U <;> by_cases hb : b∈U
  · simp [sides,ha,hb]
  · simp [sides,Finset.insert_comm a b,Finset.insert_eq_of_mem ha,Finset.erase_insert hb]
  · simp [sides,Finset.insert_eq_of_mem hb,Finset.erase_insert ha]
  · have e : ((insert a (insert b U)).erase a).erase b = U := by
      ext x
      by_cases h : x∈U
      · have ea : x≠a := fun e => ha (e ▸ h)
        have eb : x≠b := fun e => hb (e ▸ h)
        simp [h,ea,eb]
      · simp [h]; aesop
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton.mpr e.symm)))

-- With k gates left, at most k + 1 distinct signals can still be needed.
-- A split can retain either operand for later uses.
def search : Nat → Pool → Bool
  | 0,S => decide (318 ∈ S)
  | k+1,S => decide (S.card ≤ k+2 ∧ Separates S) &&
    (decide (318 ∈ S) || decide (∃ a ∈ S, ∃ b ∈ S, a < b ∧
      ∃ op ∈ [false,true], let c := combine op a b
      c ∉ S ∧ ∃ U ∈ sides S a b, search k (insert c U) = true))

def Good (S : Pool) (k : Nat) := S.card ≤ k+1 ∧ Separates S ∧ search k S=true

lemma terminal (k : Nat) : Good {318} k := by
  have h : Separates {318} := by decide
  cases k <;> simp [Good,search] <;> exact h

lemma separates_back {U : Pool} {a b : Nat} (op : Bool)
    (h : Separates (insert (combine op a b) U)) : Separates (insert a (insert b U)) := by
  intro p hp n hn
  obtain ⟨w,hw,yes,no⟩ := h p hp n hn
  rcases Finset.mem_insert.mp hw with eq|mem
  · subst w
    cases op <;> simp [combine] at yes no
    · cases ha : a.testBit n with
      | false => exact ⟨a,by simp,yes.1,ha⟩
      | true => exact ⟨b,by simp,yes.2,no ha⟩
    · rcases yes with ha|hb
      · exact ⟨a,by simp,ha,no.1⟩
      · exact ⟨b,by simp,hb,no.2⟩
  · exact ⟨w,by simp [mem],yes,no⟩

lemma good_step {k : Nat} {U : Pool} {a b : Nat} (lt : a<b) (op : Bool)
    (new : combine op a b ∉ insert a (insert b U)) (child : Good (insert (combine op a b) U) k) :
    Good (insert a (insert b U)) (k+1) := by
  let S := insert a (insert b U)
  have cn : combine op a b ∉ U := fun h => new (by simp [h])
  have card := child.1
  rw [Finset.card_insert_of_notMem cn] at card
  have h1 := Finset.card_insert_le a (insert b U)
  have h2 := Finset.card_insert_le b U
  have bound : S.card ≤ k+2 := by dsimp [S]; omega
  have sep := separates_back op child.2.1
  refine ⟨bound,sep,?_⟩
  simp only [search,Bool.and_eq_true,decide_eq_true_eq,Bool.or_eq_true]
  exact ⟨⟨bound,sep⟩,Or.inr ⟨a,by simp,b,by simp,lt,op,by cases op <;> simp,new,U,sides_mem a b,child.2.2⟩⟩

def Possible (P : Pool) (k : Nat) := ∃ d ≤ k, ∃ S ⊆ P, Good S d

lemma mono_time {P : Pool} {k j : Nat} (h : Possible P k) (le : k≤j) : Possible P j := by
  obtain ⟨d,hd,S,sub,g⟩ := h
  exact ⟨d,hd.trans le,S,sub,g⟩

-- Trace the needed signals backwards. A used gate replaces its result by both
-- operands, increasing the number of needed signals by at most one.
lemma contract_sorted {P : Pool} {a b : Nat} (ha : a∈P) (hb : b∈P) (lt : a<b) (op : Bool)
    {k : Nat} (h : Possible (insert (combine op a b) P) k) : Possible P (k+1) := by
  let c := combine op a b
  by_cases hc : c∈P
  · change Possible (insert c P) k at h
    rw [Finset.insert_eq_of_mem hc] at h
    exact mono_time h (by omega)
  obtain ⟨d,hd,T,sub,g⟩ := h
  by_cases inT : c∈T
  · let U := T.erase c
    have us : U ⊆ P := by
      intro w hw
      have hh := Finset.mem_erase.mp hw
      exact (Finset.mem_insert.mp (sub hh.2)).resolve_left hh.1
    have sub' : insert a (insert b U) ⊆ P := Finset.insert_subset ha (Finset.insert_subset hb us)
    have child : Good (insert c U) d := by simpa only [U,Finset.insert_erase inT] using g
    exact ⟨d+1,by omega,_,sub',good_step lt op (fun hw => hc (sub' hw)) child⟩
  · refine ⟨d,by omega,T,?_,g⟩
    intro w hw
    exact (Finset.mem_insert.mp (sub hw)).resolve_left (fun eq => inT (show combine op a b ∈ T from eq ▸ hw))

lemma contract {P : Pool} {a b : Nat} (ha : a∈P) (hb : b∈P) (op : Bool)
    {k : Nat} (h : Possible (insert (combine op a b) P) k) : Possible P (k+1) := by
  rcases lt_trichotomy a b with lt|rfl|gt
  · exact contract_sorted ha hb lt op h
  · have eq : combine op a a=a := by cases op <;> simp [combine]
    rw [eq,Finset.insert_eq_of_mem ha] at h
    exact mono_time h (by omega)
  · apply contract_sorted hb ha gt op
    have eq : combine op b a=combine op a b := by cases op <;> simp [combine,Nat.and_comm,Nat.or_comm]
    simpa only [eq] using h

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def inputs (p : Fin 16) : List Bool := oneEach (⟨p.val / 4,by omega⟩ : Fin 4) (⟨p.val % 4,by omega⟩ : Fin 4)
-- Each mask records one wire on the sixteen promised inputs.
def Signal (w : Nat) (f : Fin 16 → Bool) := (∀ i : Nat, 16 ≤ i → w.testBit i=false) ∧ ∀ p, w.testBit p.val=f p
def Models (P : Pool) (x : Fin 16 → List Bool) := ∀ i : Nat, ∃ w∈P, Signal w (fun p => (x p).getD i false)
def step (x : List Bool) (g : Gate) := x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]

lemma small_off {w i : Nat} (hw : w<65536) (hi : 16 ≤ i) : w.testBit i=false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (show w<2^16 from hw) (Nat.pow_le_pow_right (by decide) hi))

lemma initial : Models raw inputs := by
  let ports : List Nat := [15,240,3840,61440,4369,8738,17476,34952]
  have good : ∀ i : Fin 8, ports.getD i.val 0∈raw ∧ ports.getD i.val 0<65536 ∧
      ∀ p : Fin 16,(ports.getD i.val 0).testBit p.val=(inputs p).getD i.val false := by decide
  intro i
  by_cases hi : i<8
  · obtain ⟨m,b,e⟩ := good ⟨i,hi⟩
    exact ⟨_,m,fun _ h => small_off b h,e⟩
  · refine ⟨0,by decide,fun _ _ => by simp,fun p => ?_⟩
    have len : (inputs p).length=8 := by simp [inputs,oneEach]
    simp only [Nat.zero_testBit]
    exact (List.getD_eq_default _ _ (by omega)).symm

lemma combine_signal {a b : Nat} {f h : Fin 16 → Bool} (ha : Signal a f) (hb : Signal b h) (op : Bool) :
    Signal (combine op a b) (fun p => if op then f p || h p else f p && h p) := by
  constructor
  · intro i hi
    cases op <;> simp [combine,ha.1 i hi,hb.1 i hi]
  · intro p
    cases op <;> simp [combine,ha.2 p,hb.2 p]

lemma extend {P Q : Pool} {x : Fin 16 → List Bool} (h : Models P x) (sub : P⊆Q)
    {w : Nat} (hw : w∈Q) {f : Fin 16 → Bool} (sf : Signal w f)
    {j : Nat} (len : ∀p,(x p).length=j) : Models Q (fun p => x p ++ [f p]) := by
  intro i
  by_cases eq : i=j
  · subst i
    refine ⟨w,hw,sf.1,fun p => ?_⟩
    rw [sf.2 p,← len p]
    simp [List.getD_eq_getElem?_getD]
  · obtain ⟨v,hv,sv⟩ := h i
    refine ⟨v,sub hv,sv.1,fun p => ?_⟩
    rw [sv.2 p]
    by_cases lt : i < (x p).length
    · simp [List.getD_eq_getElem?_getD,List.getElem?_append_left lt]
    · have ge : (x p ++ [f p]).length ≤ i := by simp [len p] at *;omega
      change (x p).getD i false = (x p ++ [f p]).getD i false
      rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ ge]

lemma model_step {P : Pool} {x : Fin 16 → List Bool} {g : Gate} (m : Models P x) {j : Nat}
    (len : ∀p,(x p).length=j) (hz : 0∈P) (ht : 65535∈P)
    (mono : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length≤2) :
    ∃ Q : Pool, P⊆Q ∧ Models Q (fun p => step (x p) g) ∧
      ∀ k, Possible Q k → Possible P (k+1) := by
  obtain ⟨op,ins⟩ := g
  obtain ⟨hop,hl⟩ := mono
  change op=.and ∨ op=.or at hop
  change ins.length≤2 at hl
  match ins, hl with
  | [], _ =>
    refine ⟨P,fun _ h => h,?_,fun _ h => mono_time h (by omega)⟩
    rcases hop with rfl|rfl
    · apply extend m (fun _ h => h) ht _ len
      exact ⟨fun _ h => small_off (by decide) h,show ∀p : Fin 16,(65535 : Nat).testBit p.val=true by decide⟩
    · apply extend m (fun _ h => h) hz _ len
      exact ⟨fun _ _ => by simp,show ∀p : Fin 16,(0 : Nat).testBit p.val=false by decide⟩
  | [i], _ =>
    obtain ⟨w,hw,hs⟩ := m i
    refine ⟨P,fun _ h => h,?_,fun _ h => mono_time h (by omega)⟩
    rcases hop with rfl|rfl <;> simpa [step,GateOp.eval] using extend m (fun _ h => h) hw hs len
  | [i,j], _ =>
    obtain ⟨a,ha,sa⟩ := m i
    obtain ⟨b,hb,sb⟩ := m j
    let op' := match op with | .or => true | _ => false
    let c := combine op' a b
    have sub : P ⊆ insert c P := Finset.subset_insert _ _
    refine ⟨insert c P,sub,?_,fun _ h => contract ha hb op' h⟩
    have next := extend m sub (Finset.mem_insert_self c P) (combine_signal sa sb op') len
    rcases hop with rfl|rfl <;> simpa [step,op',GateOp.eval] using next
  | _::_::_::_, le => simp at le

lemma simulate (gs : List Gate) (P : Pool) (x : Fin 16 → List Bool) (j o : Nat)
    (hz : 0∈P) (ht : 65535∈P) (m : Models P x) (len : ∀p,(x p).length=j)
    (mono : ∀g∈gs,g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length≤2)
    (ev : ∀ p : Fin 16,(gs.foldl step (x p)).getD o false=(318 : Nat).testBit p.val) :
    Possible P gs.length := by
  induction gs generalizing P x j with
  | nil =>
    obtain ⟨w,hw,sw⟩ := m o
    have eq : w=318 := by
      apply Nat.eq_of_testBit_eq
      intro i
      by_cases lt : i<16
      · exact (sw.2 ⟨i,lt⟩).trans (ev ⟨i,lt⟩)
      · rw [sw.1 i (by omega),small_off (by decide : 318<65536) (by omega)]
    exact ⟨0,by decide,{318},Finset.singleton_subset_iff.mpr (eq ▸ hw),terminal 0⟩
  | cons g gs ih =>
    obtain ⟨Q,sub,m',back⟩ := model_step m len hz ht (mono g (by simp))
    apply back
    exact ih Q _ (j+1) (sub hz) (sub ht) m' (fun p => by simp [step,len p])
      (fun t h => mono t (by simp [h])) ev

lemma necessary (C : Circuit) (hc : Monotone2 C) (size : C.size≤7)
    (ev : Represents (fun u v : Fin 4 => (318 : Nat).testBit (4*u.val+v.val)) C) : Possible raw 7 := by
  apply mono_time (k:=C.gates.length) _ size
  apply simulate C.gates raw inputs 8 C.output (by decide) (by decide) initial (fun p => by simp [inputs,oneEach]) hc
  intro p
  have h := ev (⟨p.val / 4,by omega⟩ : Fin 4) (⟨p.val % 4,by omega⟩ : Fin 4)
  exact h.trans (congrArg (318 : Nat).testBit (Nat.div_add_mod p.val 4))

open PEqualNP.Represents PEqualNP.CircuitLowerBounds

def graph (u v : Fin 4) := (318 : Nat).testBit (4*u.val+v.val)

theorem upper : RepSizeAtMost graph 8 := by
  refine ⟨⟨[⟨.or,[5,6]⟩, ⟨.or,[8,7]⟩, ⟨.and,[0,9]⟩, ⟨.or,[4,5]⟩,
    ⟨.and,[1,11]⟩, ⟨.and,[2,4]⟩, ⟨.or,[10,12]⟩, ⟨.or,[14,13]⟩],15⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp

abbrev admitted (k : Nat) (S : Pool) := S.card ≤ k+1 ∧ Separates S

def closed (k : Nat) (S : Pool) (next : List Pool) : Bool :=
  decide (∀ a ∈ S, ∀ b ∈ S, a<b → ∀ op ∈ [false,true], let c := combine op a b
    c∉S → ∀ U ∈ sides S a b, admitted k (insert c U) → insert c U ∈ next)

lemma exclude (k : Nat) (S : Pool) (next : List Pool) (not_hit : 318 ∉ S)
    (all_children : closed (k+1) S next=true)
    (done : ∀ U∈next, search (k+1) U=false) : search (k+2) S=false := by
  by_contra! yes
  have ok : search (k+2) S=true := by simpa using yes
  rw [search] at ok
  simp only [Bool.and_eq_true,decide_eq_true_eq,Bool.or_eq_true] at ok
  rcases ok.2 with mem|⟨a,ha,b,hb,lt,op,ho,hc,U,hu,v⟩
  · exact not_hit mem
  · have adm : admitted (k+1) (insert (combine op a b) U) := by
      have h := v
      rw [search] at h
      exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
    have sub := of_decide_eq_true all_children
    exact Bool.noConfusion (v.symm.trans (done _ (sub a ha b hb lt op ho hc U hu adm)))

-- Each finite check lists every successor that still distinguishes all positive
-- inputs from all negative inputs. Deeper states use the same recurrence directly.
theorem excluded3 : search 3 {240,4383,8738,53196}=false := by decide +kernel

theorem excluded2 : search 4 {15,240,4369,8738,53196}=false := by
  apply exclude 2 _ [{240,4383,8738,53196}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded3

theorem excluded5 : search 3 {240,4383,12066,52428}=false := by decide +kernel

theorem excluded4 : search 4 {15,240,4369,12066,52428}=false := by
  apply exclude 2 _ [{240,4383,12066,52428}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded5

theorem excluded7 : search 3 {3840,4383,8738,52476}=false := by decide +kernel

theorem excluded6 : search 4 {15,3840,4369,8738,52476}=false := by
  apply exclude 2 _ [{3840,4383,8738,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded7

theorem excluded8 : search 4 {240,3840,4383,8738,52428}=false := by
  apply exclude 2 _ [{240,4383,8738,53196},{240,4383,12066,52428},{3840,4383,8738,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded3,excluded5,excluded7⟩

theorem excluded1 : search 5 {15,240,3840,4369,8738,52428}=false := by
  apply exclude 3 _ [{15,240,4369,8738,53196},{15,240,4369,12066,52428},{15,3840,4369,8738,52476},{240,3840,4383,8738,52428}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded2,excluded4,excluded6,excluded8⟩

theorem excluded11 : search 3 {4383,8738,17652,36744}=false := by decide +kernel

theorem excluded10 : search 4 {15,4369,8738,17652,36744}=false := by
  apply exclude 2 _ [{4383,8738,17652,36744}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded11

theorem excluded12 : search 4 {240,4383,8738,17476,36744}=false := by
  apply exclude 2 _ [{240,4383,8738,53196},{4383,8738,17652,36744}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded3,excluded11⟩

theorem excluded9 : search 5 {15,240,4369,8738,17476,36744}=false := by
  apply exclude 3 _ [{15,240,4369,8738,53196},{15,4369,8738,17652,36744},{240,4383,8738,17476,36744}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded2,excluded10,excluded12⟩

theorem excluded15 : search 3 {4383,8738,20292,35064}=false := by decide +kernel

theorem excluded14 : search 4 {15,4369,8738,20292,35064}=false := by
  apply exclude 2 _ [{4383,8738,20292,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded15

theorem excluded16 : search 4 {240,4383,8738,20292,34952}=false := by
  apply exclude 2 _ [{240,4383,8738,53196},{4383,8738,20292,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded3,excluded15⟩

theorem excluded13 : search 5 {15,240,4369,8738,20292,34952}=false := by
  apply exclude 3 _ [{15,240,4369,8738,53196},{15,4369,8738,20292,35064},{240,4383,8738,20292,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded2,excluded14,excluded16⟩

theorem excluded18 : search 4 {240,4383,12066,17476,34952}=false := by
  apply exclude 2 _ [{240,4383,12066,52428}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded5

theorem excluded17 : search 5 {15,240,4369,12066,17476,34952}=false := by
  apply exclude 3 _ [{15,240,4369,12066,52428},{240,4383,12066,17476,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded4,excluded18⟩

theorem excluded20 : search 4 {3840,4383,8738,17476,35064}=false := by
  apply exclude 2 _ [{3840,4383,8738,52476},{4383,8738,20292,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded7,excluded15⟩

theorem excluded19 : search 5 {15,3840,4369,8738,17476,35064}=false := by
  apply exclude 3 _ [{15,3840,4369,8738,52476},{15,4369,8738,20292,35064},{3840,4383,8738,17476,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded6,excluded14,excluded20⟩

theorem excluded22 : search 4 {3840,4383,8738,17652,34952}=false := by
  apply exclude 2 _ [{3840,4383,8738,52476},{4383,8738,17652,36744}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded7,excluded11⟩

theorem excluded21 : search 5 {15,3840,4369,8738,17652,34952}=false := by
  apply exclude 3 _ [{15,3840,4369,8738,52476},{15,4369,8738,17652,36744},{3840,4383,8738,17652,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded6,excluded10,excluded22⟩

theorem excluded23 : search 5 {240,3840,4383,8738,17476,34952}=false := by
  apply exclude 3 _ [{240,3840,4383,8738,52428},{240,4383,8738,17476,36744},{240,4383,8738,20292,34952},{240,4383,12066,17476,34952},{3840,4383,8738,17476,35064},{3840,4383,8738,17652,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded8,excluded12,excluded16,excluded18,excluded20,excluded22⟩

theorem excluded0 : search 6 {15,240,3840,4369,8738,17476,34952}=false := by
  apply exclude 4 _ [{15,240,3840,4369,8738,52428},{15,240,4369,8738,17476,36744},{15,240,4369,8738,20292,34952},{15,240,4369,12066,17476,34952},{15,3840,4369,8738,17476,35064},{15,3840,4369,8738,17652,34952},{240,3840,4383,8738,17476,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded1,excluded9,excluded13,excluded17,excluded19,excluded21,excluded23⟩

theorem excluded28 : search 3 {240,4383,8738,36748}=false := by decide +kernel

theorem excluded29 : search 3 {240,4383,8742,36744}=false := by decide +kernel

theorem excluded30 : search 3 {244,4383,8738,36744}=false := by decide +kernel

theorem excluded27 : search 4 {4,240,4383,8738,36744}=false := by
  apply exclude 2 _ [{240,4383,8738,36748},{240,4383,8742,36744},{244,4383,8738,36744}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded28,excluded29,excluded30⟩

theorem excluded31 : search 4 {15,240,4369,8738,36748}=false := by
  apply exclude 2 _ [{240,4383,8738,36748}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded28

theorem excluded32 : search 4 {15,240,4369,8742,36744}=false := by
  apply exclude 2 _ [{240,4383,8742,36744}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded29

theorem excluded33 : search 4 {15,244,4369,8738,36744}=false := by
  apply exclude 2 _ [{244,4383,8738,36744}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded30

theorem excluded26 : search 5 {4,15,240,4369,8738,36744}=false := by
  apply exclude 3 _ [{4,240,4383,8738,36744},{15,240,4369,8738,36748},{15,240,4369,8742,36744},{15,244,4369,8738,36744}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded27,excluded31,excluded32,excluded33⟩

theorem excluded36 : search 3 {240,4383,12066,34956}=false := by decide +kernel

theorem excluded37 : search 3 {240,4383,12070,34952}=false := by decide +kernel

theorem excluded38 : search 3 {244,4383,12066,34952}=false := by decide +kernel

theorem excluded35 : search 4 {4,240,4383,12066,34952}=false := by
  apply exclude 2 _ [{240,4383,12066,34956},{240,4383,12070,34952},{244,4383,12066,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded36,excluded37,excluded38⟩

theorem excluded39 : search 4 {15,240,4369,12066,34956}=false := by
  apply exclude 2 _ [{240,4383,12066,34956}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded36

theorem excluded40 : search 4 {15,240,4369,12070,34952}=false := by
  apply exclude 2 _ [{240,4383,12070,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded37

theorem excluded41 : search 4 {15,244,4369,12066,34952}=false := by
  apply exclude 2 _ [{244,4383,12066,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded38

theorem excluded34 : search 5 {4,15,240,4369,12066,34952}=false := by
  apply exclude 3 _ [{4,240,4383,12066,34952},{15,240,4369,12066,34956},{15,240,4369,12070,34952},{15,244,4369,12066,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded35,excluded39,excluded40,excluded41⟩

theorem excluded44 : search 3 {3840,4383,8738,35068}=false := by decide +kernel

theorem excluded45 : search 3 {3840,4383,8742,35064}=false := by decide +kernel

theorem excluded46 : search 3 {3844,4383,8738,35064}=false := by decide +kernel

theorem excluded43 : search 4 {4,3840,4383,8738,35064}=false := by
  apply exclude 2 _ [{3840,4383,8738,35068},{3840,4383,8742,35064},{3844,4383,8738,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded44,excluded45,excluded46⟩

theorem excluded47 : search 4 {15,3840,4369,8738,35068}=false := by
  apply exclude 2 _ [{3840,4383,8738,35068}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded44

theorem excluded48 : search 4 {15,3840,4369,8742,35064}=false := by
  apply exclude 2 _ [{3840,4383,8742,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded45

theorem excluded49 : search 4 {15,3844,4369,8738,35064}=false := by
  apply exclude 2 _ [{3844,4383,8738,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded46

theorem excluded42 : search 5 {4,15,3840,4369,8738,35064}=false := by
  apply exclude 3 _ [{4,3840,4383,8738,35064},{15,3840,4369,8738,35068},{15,3840,4369,8742,35064},{15,3844,4369,8738,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded43,excluded47,excluded48,excluded49⟩

theorem excluded51 : search 4 {240,3840,4383,8738,34956}=false := by
  apply exclude 2 _ [{240,4383,8738,36748},{240,4383,12066,34956},{3840,4383,8738,35068}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded28,excluded36,excluded44⟩

theorem excluded52 : search 4 {240,3840,4383,8742,34952}=false := by
  apply exclude 2 _ [{240,4383,8742,36744},{240,4383,12070,34952},{3840,4383,8742,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded29,excluded37,excluded45⟩

theorem excluded53 : search 4 {240,3844,4383,8738,34952}=false := by
  apply exclude 2 _ [{240,4383,8738,36748},{240,4383,12070,34952},{3844,4383,8738,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded28,excluded37,excluded46⟩

theorem excluded54 : search 4 {244,3840,4383,8738,34952}=false := by
  apply exclude 2 _ [{244,4383,8738,36744},{244,4383,12066,34952},{3840,4383,8738,35068}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded30,excluded38,excluded44⟩

theorem excluded50 : search 5 {4,240,3840,4383,8738,34952}=false := by
  apply exclude 3 _ [{4,240,4383,8738,36744},{4,240,4383,12066,34952},{4,3840,4383,8738,35064},{240,3840,4383,8738,34956},{240,3840,4383,8742,34952},{240,3844,4383,8738,34952},{244,3840,4383,8738,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded27,excluded35,excluded43,excluded51,excluded52,excluded53,excluded54⟩

theorem excluded55 : search 5 {15,240,3840,4369,8738,34956}=false := by
  apply exclude 3 _ [{15,240,4369,8738,36748},{15,240,4369,12066,34956},{15,3840,4369,8738,35068},{240,3840,4383,8738,34956}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded31,excluded39,excluded47,excluded51⟩

theorem excluded56 : search 5 {15,240,3840,4369,8742,34952}=false := by
  apply exclude 3 _ [{15,240,4369,8742,36744},{15,240,4369,12070,34952},{15,3840,4369,8742,35064},{240,3840,4383,8742,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded32,excluded40,excluded48,excluded52⟩

theorem excluded57 : search 5 {15,240,3844,4369,8738,34952}=false := by
  apply exclude 3 _ [{15,240,4369,8738,36748},{15,240,4369,12070,34952},{15,3844,4369,8738,35064},{240,3844,4383,8738,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded31,excluded40,excluded49,excluded53⟩

theorem excluded58 : search 5 {15,244,3840,4369,8738,34952}=false := by
  apply exclude 3 _ [{15,244,4369,8738,36744},{15,244,4369,12066,34952},{15,3840,4369,8738,35068},{244,3840,4383,8738,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded33,excluded41,excluded47,excluded54⟩

theorem excluded25 : search 6 {4,15,240,3840,4369,8738,34952}=false := by
  apply exclude 4 _ [{4,15,240,4369,8738,36744},{4,15,240,4369,12066,34952},{4,15,3840,4369,8738,35064},{4,240,3840,4383,8738,34952},{15,240,3840,4369,8738,34956},{15,240,3840,4369,8742,34952},{15,240,3844,4369,8738,34952},{15,244,3840,4369,8738,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded26,excluded34,excluded42,excluded50,excluded55,excluded56,excluded57,excluded58⟩

theorem excluded62 : search 3 {240,4383,8738,20300}=false := by decide +kernel

theorem excluded63 : search 3 {240,4383,8746,20292}=false := by decide +kernel

theorem excluded64 : search 3 {248,4383,8738,20292}=false := by decide +kernel

theorem excluded61 : search 4 {8,240,4383,8738,20292}=false := by
  apply exclude 2 _ [{240,4383,8738,20300},{240,4383,8746,20292},{248,4383,8738,20292}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded62,excluded63,excluded64⟩

theorem excluded65 : search 4 {15,240,4369,8738,20300}=false := by
  apply exclude 2 _ [{240,4383,8738,20300}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded62

theorem excluded66 : search 4 {15,240,4369,8746,20292}=false := by
  apply exclude 2 _ [{240,4383,8746,20292}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded63

theorem excluded67 : search 4 {15,248,4369,8738,20292}=false := by
  apply exclude 2 _ [{248,4383,8738,20292}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded64

theorem excluded60 : search 5 {8,15,240,4369,8738,20292}=false := by
  apply exclude 3 _ [{8,240,4383,8738,20292},{15,240,4369,8738,20300},{15,240,4369,8746,20292},{15,248,4369,8738,20292}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded61,excluded65,excluded66,excluded67⟩

theorem excluded70 : search 3 {240,4383,12066,17484}=false := by decide +kernel

theorem excluded71 : search 3 {240,4383,12074,17476}=false := by decide +kernel

theorem excluded72 : search 3 {248,4383,12066,17476}=false := by decide +kernel

theorem excluded69 : search 4 {8,240,4383,12066,17476}=false := by
  apply exclude 2 _ [{240,4383,12066,17484},{240,4383,12074,17476},{248,4383,12066,17476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded70,excluded71,excluded72⟩

theorem excluded73 : search 4 {15,240,4369,12066,17484}=false := by
  apply exclude 2 _ [{240,4383,12066,17484}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded70

theorem excluded74 : search 4 {15,240,4369,12074,17476}=false := by
  apply exclude 2 _ [{240,4383,12074,17476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded71

theorem excluded75 : search 4 {15,248,4369,12066,17476}=false := by
  apply exclude 2 _ [{248,4383,12066,17476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded72

theorem excluded68 : search 5 {8,15,240,4369,12066,17476}=false := by
  apply exclude 3 _ [{8,240,4383,12066,17476},{15,240,4369,12066,17484},{15,240,4369,12074,17476},{15,248,4369,12066,17476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded69,excluded73,excluded74,excluded75⟩

theorem excluded78 : search 3 {3840,4383,8738,17660}=false := by decide +kernel

theorem excluded79 : search 3 {3840,4383,8746,17652}=false := by decide +kernel

theorem excluded80 : search 3 {3848,4383,8738,17652}=false := by decide +kernel

theorem excluded77 : search 4 {8,3840,4383,8738,17652}=false := by
  apply exclude 2 _ [{3840,4383,8738,17660},{3840,4383,8746,17652},{3848,4383,8738,17652}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded78,excluded79,excluded80⟩

theorem excluded81 : search 4 {15,3840,4369,8738,17660}=false := by
  apply exclude 2 _ [{3840,4383,8738,17660}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded78

theorem excluded82 : search 4 {15,3840,4369,8746,17652}=false := by
  apply exclude 2 _ [{3840,4383,8746,17652}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded79

theorem excluded83 : search 4 {15,3848,4369,8738,17652}=false := by
  apply exclude 2 _ [{3848,4383,8738,17652}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded80

theorem excluded76 : search 5 {8,15,3840,4369,8738,17652}=false := by
  apply exclude 3 _ [{8,3840,4383,8738,17652},{15,3840,4369,8738,17660},{15,3840,4369,8746,17652},{15,3848,4369,8738,17652}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded77,excluded81,excluded82,excluded83⟩

theorem excluded85 : search 4 {240,3840,4383,8738,17484}=false := by
  apply exclude 2 _ [{240,4383,8738,20300},{240,4383,12066,17484},{3840,4383,8738,17660}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded62,excluded70,excluded78⟩

theorem excluded86 : search 4 {240,3840,4383,8746,17476}=false := by
  apply exclude 2 _ [{240,4383,8746,20292},{240,4383,12074,17476},{3840,4383,8746,17652}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded63,excluded71,excluded79⟩

theorem excluded87 : search 4 {240,3848,4383,8738,17476}=false := by
  apply exclude 2 _ [{240,4383,8738,20300},{240,4383,12074,17476},{3848,4383,8738,17652}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded62,excluded71,excluded80⟩

theorem excluded88 : search 4 {248,3840,4383,8738,17476}=false := by
  apply exclude 2 _ [{248,4383,8738,20292},{248,4383,12066,17476},{3840,4383,8738,17660}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded64,excluded72,excluded78⟩

theorem excluded84 : search 5 {8,240,3840,4383,8738,17476}=false := by
  apply exclude 3 _ [{8,240,4383,8738,20292},{8,240,4383,12066,17476},{8,3840,4383,8738,17652},{240,3840,4383,8738,17484},{240,3840,4383,8746,17476},{240,3848,4383,8738,17476},{248,3840,4383,8738,17476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded61,excluded69,excluded77,excluded85,excluded86,excluded87,excluded88⟩

theorem excluded89 : search 5 {15,240,3840,4369,8738,17484}=false := by
  apply exclude 3 _ [{15,240,4369,8738,20300},{15,240,4369,12066,17484},{15,3840,4369,8738,17660},{240,3840,4383,8738,17484}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded65,excluded73,excluded81,excluded85⟩

theorem excluded90 : search 5 {15,240,3840,4369,8746,17476}=false := by
  apply exclude 3 _ [{15,240,4369,8746,20292},{15,240,4369,12074,17476},{15,3840,4369,8746,17652},{240,3840,4383,8746,17476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded66,excluded74,excluded82,excluded86⟩

theorem excluded91 : search 5 {15,240,3848,4369,8738,17476}=false := by
  apply exclude 3 _ [{15,240,4369,8738,20300},{15,240,4369,12074,17476},{15,3848,4369,8738,17652},{240,3848,4383,8738,17476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded65,excluded74,excluded83,excluded87⟩

theorem excluded92 : search 5 {15,248,3840,4369,8738,17476}=false := by
  apply exclude 3 _ [{15,248,4369,8738,20292},{15,248,4369,12066,17476},{15,3840,4369,8738,17660},{248,3840,4383,8738,17476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded67,excluded75,excluded81,excluded88⟩

theorem excluded59 : search 6 {8,15,240,3840,4369,8738,17476}=false := by
  apply exclude 4 _ [{8,15,240,4369,8738,20292},{8,15,240,4369,12066,17476},{8,15,3840,4369,8738,17652},{8,240,3840,4383,8738,17476},{15,240,3840,4369,8738,17484},{15,240,3840,4369,8746,17476},{15,240,3848,4369,8738,17476},{15,248,3840,4369,8738,17476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded60,excluded68,excluded76,excluded84,excluded89,excluded90,excluded91,excluded92⟩

theorem excluded96 : search 3 {15,4369,8738,52732}=false := by decide +kernel

theorem excluded97 : search 3 {240,4383,8738,52684}=false := by decide +kernel

theorem excluded95 : search 4 {15,240,4369,8738,52684}=false := by
  apply exclude 2 _ [{15,4369,8738,52732},{240,4383,8738,52684}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded96,excluded97⟩

theorem excluded99 : search 3 {15,4369,8994,52476}=false := by decide +kernel

theorem excluded100 : search 3 {240,4383,8994,52428}=false := by decide +kernel

theorem excluded98 : search 4 {15,240,4369,8994,52428}=false := by
  apply exclude 2 _ [{15,4369,8994,52476},{240,4383,8994,52428}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded99,excluded100⟩

theorem excluded102 : search 3 {256,4383,8738,52476}=false := by decide +kernel

theorem excluded101 : search 4 {15,256,4369,8738,52476}=false := by
  apply exclude 2 _ [{15,4369,8738,52732},{15,4369,8994,52476},{256,4383,8738,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded96,excluded99,excluded102⟩

theorem excluded104 : search 3 {496,4383,8738,52428}=false := by decide +kernel

theorem excluded103 : search 4 {15,496,4369,8738,52428}=false := by
  apply exclude 2 _ [{15,4369,8738,52732},{496,4383,8738,52428}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded96,excluded104⟩

theorem excluded105 : search 4 {240,256,4383,8738,52428}=false := by
  apply exclude 2 _ [{240,4383,8738,52684},{240,4383,8994,52428},{256,4383,8738,52476},{496,4383,8738,52428}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded97,excluded100,excluded102,excluded104⟩

theorem excluded94 : search 5 {15,240,256,4369,8738,52428}=false := by
  apply exclude 3 _ [{15,240,4369,8738,52684},{15,240,4369,8994,52428},{15,256,4369,8738,52476},{15,496,4369,8738,52428},{240,256,4383,8738,52428}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded95,excluded98,excluded101,excluded103,excluded105⟩

theorem excluded108 : search 3 {4383,8738,17476,35320}=false := by decide +kernel

theorem excluded107 : search 4 {15,4369,8738,17476,35320}=false := by
  apply exclude 2 _ [{15,4369,8738,52732},{4383,8738,17476,35320}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded96,excluded108⟩

theorem excluded110 : search 3 {4383,8738,17652,35208}=false := by decide +kernel

theorem excluded109 : search 4 {15,4369,8738,17652,35208}=false := by
  apply exclude 2 _ [{15,4369,8738,52732},{4383,8738,17652,35208}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded96,excluded110⟩

theorem excluded111 : search 4 {240,4383,8738,17476,35208}=false := by
  apply exclude 2 _ [{240,4383,8738,52684},{4383,8738,17476,35320},{4383,8738,17652,35208}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded97,excluded108,excluded110⟩

theorem excluded106 : search 5 {15,240,4369,8738,17476,35208}=false := by
  apply exclude 3 _ [{15,240,4369,8738,52684},{15,4369,8738,17476,35320},{15,4369,8738,17652,35208},{240,4383,8738,17476,35208}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded95,excluded107,excluded109,excluded111⟩

theorem excluded114 : search 3 {4383,8738,17732,35064}=false := by decide +kernel

theorem excluded113 : search 4 {15,4369,8738,17732,35064}=false := by
  apply exclude 2 _ [{15,4369,8738,52732},{4383,8738,17732,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded96,excluded114⟩

theorem excluded116 : search 3 {4383,8738,17908,34952}=false := by decide +kernel

theorem excluded115 : search 4 {15,4369,8738,17908,34952}=false := by
  apply exclude 2 _ [{15,4369,8738,52732},{4383,8738,17908,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded96,excluded116⟩

theorem excluded117 : search 4 {240,4383,8738,17732,34952}=false := by
  apply exclude 2 _ [{240,4383,8738,52684},{4383,8738,17732,35064},{4383,8738,17908,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded97,excluded114,excluded116⟩

theorem excluded112 : search 5 {15,240,4369,8738,17732,34952}=false := by
  apply exclude 3 _ [{15,240,4369,8738,52684},{15,4369,8738,17732,35064},{15,4369,8738,17908,34952},{240,4383,8738,17732,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded95,excluded113,excluded115,excluded117⟩

theorem excluded120 : search 3 {4383,8994,17476,35064}=false := by decide +kernel

theorem excluded119 : search 4 {15,4369,8994,17476,35064}=false := by
  apply exclude 2 _ [{15,4369,8994,52476},{4383,8994,17476,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded99,excluded120⟩

theorem excluded122 : search 3 {4383,8994,17652,34952}=false := by decide +kernel

theorem excluded121 : search 4 {15,4369,8994,17652,34952}=false := by
  apply exclude 2 _ [{15,4369,8994,52476},{4383,8994,17652,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded99,excluded122⟩

theorem excluded123 : search 4 {240,4383,8994,17476,34952}=false := by
  apply exclude 2 _ [{240,4383,8994,52428},{4383,8994,17476,35064},{4383,8994,17652,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded100,excluded120,excluded122⟩

theorem excluded118 : search 5 {15,240,4369,8994,17476,34952}=false := by
  apply exclude 3 _ [{15,240,4369,8994,52428},{15,4369,8994,17476,35064},{15,4369,8994,17652,34952},{240,4383,8994,17476,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded98,excluded119,excluded121,excluded123⟩

theorem excluded125 : search 4 {256,4383,8738,17476,35064}=false := by
  apply exclude 2 _ [{256,4383,8738,52476},{4383,8738,17476,35320},{4383,8738,17732,35064},{4383,8994,17476,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded102,excluded108,excluded114,excluded120⟩

theorem excluded124 : search 5 {15,256,4369,8738,17476,35064}=false := by
  apply exclude 3 _ [{15,256,4369,8738,52476},{15,4369,8738,17476,35320},{15,4369,8738,17732,35064},{15,4369,8994,17476,35064},{256,4383,8738,17476,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded101,excluded107,excluded113,excluded119,excluded125⟩

theorem excluded127 : search 4 {256,4383,8738,17652,34952}=false := by
  apply exclude 2 _ [{256,4383,8738,52476},{4383,8738,17652,35208},{4383,8738,17908,34952},{4383,8994,17652,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded102,excluded110,excluded116,excluded122⟩

theorem excluded126 : search 5 {15,256,4369,8738,17652,34952}=false := by
  apply exclude 3 _ [{15,256,4369,8738,52476},{15,4369,8738,17652,35208},{15,4369,8738,17908,34952},{15,4369,8994,17652,34952},{256,4383,8738,17652,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded101,excluded109,excluded115,excluded121,excluded127⟩

theorem excluded129 : search 4 {496,4383,8738,17476,34952}=false := by
  apply exclude 2 _ [{496,4383,8738,52428},{4383,8738,17476,35320},{4383,8738,17908,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded104,excluded108,excluded116⟩

theorem excluded128 : search 5 {15,496,4369,8738,17476,34952}=false := by
  apply exclude 3 _ [{15,496,4369,8738,52428},{15,4369,8738,17476,35320},{15,4369,8738,17908,34952},{496,4383,8738,17476,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded103,excluded107,excluded115,excluded129⟩

theorem excluded130 : search 5 {240,256,4383,8738,17476,34952}=false := by
  apply exclude 3 _ [{240,256,4383,8738,52428},{240,4383,8738,17476,35208},{240,4383,8738,17732,34952},{240,4383,8994,17476,34952},{256,4383,8738,17476,35064},{256,4383,8738,17652,34952},{496,4383,8738,17476,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded105,excluded111,excluded117,excluded123,excluded125,excluded127,excluded129⟩

theorem excluded93 : search 6 {15,240,256,4369,8738,17476,34952}=false := by
  apply exclude 4 _ [{15,240,256,4369,8738,52428},{15,240,4369,8738,17476,35208},{15,240,4369,8738,17732,34952},{15,240,4369,8994,17476,34952},{15,256,4369,8738,17476,35064},{15,256,4369,8738,17652,34952},{15,496,4369,8738,17476,34952},{240,256,4383,8738,17476,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded94,excluded106,excluded112,excluded118,excluded124,excluded126,excluded128,excluded130⟩

theorem excluded134 : search 3 {240,4383,8738,53244}=false := by decide +kernel

theorem excluded133 : search 4 {15,240,4369,8738,53244}=false := by
  apply exclude 2 _ [{240,4383,8738,53244}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded134

theorem excluded136 : search 3 {240,4383,12066,52476}=false := by decide +kernel

theorem excluded135 : search 4 {15,240,4369,12066,52476}=false := by
  apply exclude 2 _ [{240,4383,12066,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded136

theorem excluded138 : search 3 {15,272,8738,52476}=false := by decide +kernel

theorem excluded139 : search 3 {4080,4383,8738,52476}=false := by decide +kernel

theorem excluded137 : search 4 {15,4080,4369,8738,52476}=false := by
  apply exclude 2 _ [{15,272,8738,52476},{4080,4383,8738,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded138,excluded139⟩

theorem excluded140 : search 4 {240,3840,4383,8738,52476}=false := by
  apply exclude 2 _ [{240,4383,8738,53244},{240,4383,12066,52476},{4080,4383,8738,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded134,excluded136,excluded139⟩

theorem excluded132 : search 5 {15,240,3840,4369,8738,52476}=false := by
  apply exclude 3 _ [{15,240,4369,8738,53244},{15,240,4369,12066,52476},{15,4080,4369,8738,52476},{240,3840,4383,8738,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded133,excluded135,excluded137,excluded140⟩

theorem excluded143 : search 3 {4383,8738,17652,36856}=false := by decide +kernel

theorem excluded142 : search 4 {15,4369,8738,17652,36856}=false := by
  apply exclude 2 _ [{4383,8738,17652,36856}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded143

theorem excluded144 : search 4 {240,4383,8738,17476,36856}=false := by
  apply exclude 2 _ [{240,4383,8738,53244},{4383,8738,17652,36856}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded134,excluded143⟩

theorem excluded141 : search 5 {15,240,4369,8738,17476,36856}=false := by
  apply exclude 3 _ [{15,240,4369,8738,53244},{15,4369,8738,17652,36856},{240,4383,8738,17476,36856}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded133,excluded142,excluded144⟩

theorem excluded147 : search 3 {4383,8738,20468,35064}=false := by decide +kernel

theorem excluded146 : search 4 {15,4369,8738,20468,35064}=false := by
  apply exclude 2 _ [{4383,8738,20468,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded147

theorem excluded148 : search 4 {240,4383,8738,20292,35064}=false := by
  apply exclude 2 _ [{240,4383,8738,53244},{4383,8738,20468,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded134,excluded147⟩

theorem excluded145 : search 5 {15,240,4369,8738,20292,35064}=false := by
  apply exclude 3 _ [{15,240,4369,8738,53244},{15,4369,8738,20468,35064},{240,4383,8738,20292,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded133,excluded146,excluded148⟩

theorem excluded151 : search 3 {4383,12066,17652,35064}=false := by decide +kernel

theorem excluded150 : search 4 {15,4369,12066,17652,35064}=false := by
  apply exclude 2 _ [{4383,12066,17652,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded151

theorem excluded152 : search 4 {240,4383,12066,17476,35064}=false := by
  apply exclude 2 _ [{240,4383,12066,52476},{4383,12066,17652,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded136,excluded151⟩

theorem excluded149 : search 5 {15,240,4369,12066,17476,35064}=false := by
  apply exclude 3 _ [{15,240,4369,12066,52476},{15,4369,12066,17652,35064},{240,4383,12066,17476,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded135,excluded150,excluded152⟩

theorem excluded154 : search 4 {3840,4383,8738,17652,35064}=false := by
  apply exclude 2 _ [{3840,4383,8738,52476},{4383,8738,17652,36856},{4383,8738,20468,35064},{4383,12066,17652,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded7,excluded143,excluded147,excluded151⟩

theorem excluded153 : search 5 {15,3840,4369,8738,17652,35064}=false := by
  apply exclude 3 _ [{15,3840,4369,8738,52476},{15,4369,8738,17652,36856},{15,4369,8738,20468,35064},{15,4369,12066,17652,35064},{3840,4383,8738,17652,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded6,excluded142,excluded146,excluded150,excluded154⟩

theorem excluded156 : search 4 {15,272,8738,17476,35064}=false := by
  apply exclude 2 _ [{15,272,8738,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded138

theorem excluded157 : search 4 {4080,4383,8738,17476,35064}=false := by
  apply exclude 2 _ [{4080,4383,8738,52476},{4383,8738,20468,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded139,excluded147⟩

theorem excluded155 : search 5 {15,4080,4369,8738,17476,35064}=false := by
  apply exclude 3 _ [{15,272,8738,17476,35064},{15,4080,4369,8738,52476},{15,4369,8738,20468,35064},{4080,4383,8738,17476,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded156,excluded137,excluded146,excluded157⟩

theorem excluded158 : search 5 {240,3840,4383,8738,17476,35064}=false := by
  apply exclude 3 _ [{240,3840,4383,8738,52476},{240,4383,8738,17476,36856},{240,4383,8738,20292,35064},{240,4383,12066,17476,35064},{3840,4383,8738,17652,35064},{4080,4383,8738,17476,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded140,excluded144,excluded148,excluded152,excluded154,excluded157⟩

theorem excluded131 : search 6 {15,240,3840,4369,8738,17476,35064}=false := by
  apply exclude 4 _ [{15,240,3840,4369,8738,52476},{15,240,4369,8738,17476,36856},{15,240,4369,8738,20292,35064},{15,240,4369,12066,17476,35064},{15,3840,4369,8738,17652,35064},{15,4080,4369,8738,17476,35064},{240,3840,4383,8738,17476,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded132,excluded141,excluded145,excluded149,excluded153,excluded155,excluded158⟩

theorem excluded162 : search 3 {240,4383,12066,53196}=false := by decide +kernel

theorem excluded161 : search 4 {15,240,4369,12066,53196}=false := by
  apply exclude 2 _ [{240,4383,12066,53196}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded162

theorem excluded163 : search 4 {240,3840,4383,8738,53196}=false := by
  apply exclude 2 _ [{240,4383,12066,53196}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded162

theorem excluded160 : search 5 {15,240,3840,4369,8738,53196}=false := by
  apply exclude 3 _ [{15,240,4369,12066,53196},{240,3840,4383,8738,53196}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded161,excluded163⟩

theorem excluded165 : search 4 {240,4383,8738,20292,36744}=false := by
  apply exclude 2 _ [{240,4383,8738,53196}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded3

theorem excluded164 : search 5 {15,240,4369,8738,20292,36744}=false := by
  apply exclude 3 _ [{15,240,4369,8738,53196},{240,4383,8738,20292,36744}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded2,excluded165⟩

theorem excluded167 : search 4 {240,4383,12066,17476,36744}=false := by
  apply exclude 2 _ [{240,4383,12066,53196}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded162

theorem excluded166 : search 5 {15,240,4369,12066,17476,36744}=false := by
  apply exclude 3 _ [{15,240,4369,12066,53196},{240,4383,12066,17476,36744}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded161,excluded167⟩

theorem excluded169 : search 4 {3840,4383,8738,17652,36744}=false := by
  apply exclude 2 _ [] (by decide) (by decide +kernel)
  simp

theorem excluded168 : search 5 {15,3840,4369,8738,17652,36744}=false := by
  apply exclude 3 _ [{3840,4383,8738,17652,36744}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded169

theorem excluded170 : search 5 {240,3840,4383,8738,17476,36744}=false := by
  apply exclude 3 _ [{240,3840,4383,8738,53196},{240,4383,8738,20292,36744},{240,4383,12066,17476,36744},{3840,4383,8738,17652,36744}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded163,excluded165,excluded167,excluded169⟩

theorem excluded159 : search 6 {15,240,3840,4369,8738,17476,36744}=false := by
  apply exclude 4 _ [{15,240,3840,4369,8738,53196},{15,240,4369,8738,20292,36744},{15,240,4369,12066,17476,36744},{15,3840,4369,8738,17652,36744},{240,3840,4383,8738,17476,36744}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded160,excluded164,excluded166,excluded168,excluded170⟩

theorem excluded174 : search 3 {14,240,4369,12066}=false := by decide +kernel

theorem excluded173 : search 4 {14,240,3840,4369,8738}=false := by
  apply exclude 2 _ [{14,240,4369,12066}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded174

theorem excluded176 : search 3 {240,4383,8738,61422}=false := by decide +kernel

theorem excluded175 : search 4 {15,240,4369,8738,61422}=false := by
  apply exclude 2 _ [{240,4383,8738,61422}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded176

theorem excluded178 : search 3 {240,4383,12066,61166}=false := by decide +kernel

theorem excluded177 : search 4 {15,240,4369,12066,61166}=false := by
  apply exclude 2 _ [{14,240,4369,12066},{240,4383,12066,61166}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded174,excluded178⟩

theorem excluded179 : search 4 {240,3840,4383,8738,61166}=false := by
  apply exclude 2 _ [{240,4383,8738,61422},{240,4383,12066,61166}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded176,excluded178⟩

theorem excluded172 : search 5 {15,240,3840,4369,8738,61166}=false := by
  apply exclude 3 _ [{14,240,3840,4369,8738},{15,240,4369,8738,61422},{15,240,4369,12066,61166},{240,3840,4383,8738,61166}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded173,excluded175,excluded177,excluded179⟩

theorem excluded182 : search 3 {240,4383,26214,44970}=false := by decide +kernel

theorem excluded181 : search 4 {15,240,4369,26214,44970}=false := by
  apply exclude 2 _ [{240,4383,26214,44970}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded182

theorem excluded184 : search 3 {240,4383,28518,43690}=false := by decide +kernel

theorem excluded183 : search 4 {15,240,4369,28518,43690}=false := by
  apply exclude 2 _ [{240,4383,28518,43690}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded184

theorem excluded185 : search 4 {240,3840,4383,26214,43690}=false := by
  apply exclude 2 _ [{240,4383,26214,44970},{240,4383,28518,43690}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded182,excluded184⟩

theorem excluded180 : search 5 {15,240,3840,4369,26214,43690}=false := by
  apply exclude 3 _ [{15,240,4369,26214,44970},{15,240,4369,28518,43690},{240,3840,4383,26214,43690}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded181,excluded183,excluded185⟩

theorem excluded188 : search 3 {4383,8738,17652,44970}=false := by decide +kernel

theorem excluded187 : search 4 {15,4369,8738,17652,44970}=false := by
  apply exclude 2 _ [{4383,8738,17652,44970}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded188

theorem excluded189 : search 4 {240,4383,8738,17476,44970}=false := by
  apply exclude 2 _ [{240,4383,8738,61422},{240,4383,26214,44970},{4383,8738,17652,44970}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded176,excluded182,excluded188⟩

theorem excluded186 : search 5 {15,240,4369,8738,17476,44970}=false := by
  apply exclude 3 _ [{15,240,4369,8738,61422},{15,240,4369,26214,44970},{15,4369,8738,17652,44970},{240,4383,8738,17476,44970}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded175,excluded181,excluded187,excluded189⟩

theorem excluded191 : search 4 {240,4383,8738,20292,43690}=false := by
  apply exclude 2 _ [{240,4383,8738,61422},{240,4383,28518,43690}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded176,excluded184⟩

theorem excluded190 : search 5 {15,240,4369,8738,20292,43690}=false := by
  apply exclude 3 _ [{15,240,4369,8738,61422},{15,240,4369,28518,43690},{240,4383,8738,20292,43690}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded175,excluded183,excluded191⟩

theorem excluded194 : search 3 {4383,12066,17652,43690}=false := by decide +kernel

theorem excluded193 : search 4 {15,4369,12066,17652,43690}=false := by
  apply exclude 2 _ [{4383,12066,17652,43690}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded194

theorem excluded195 : search 4 {240,4383,12066,17476,43690}=false := by
  apply exclude 2 _ [{240,4383,12066,61166},{240,4383,28518,43690},{4383,12066,17652,43690}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded178,excluded184,excluded194⟩

theorem excluded192 : search 5 {15,240,4369,12066,17476,43690}=false := by
  apply exclude 3 _ [{15,240,4369,12066,61166},{15,240,4369,28518,43690},{15,4369,12066,17652,43690},{240,4383,12066,17476,43690}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded177,excluded183,excluded193,excluded195⟩

theorem excluded197 : search 4 {3840,4383,8738,17652,43690}=false := by
  apply exclude 2 _ [{4383,8738,17652,44970},{4383,12066,17652,43690}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded188,excluded194⟩

theorem excluded196 : search 5 {15,3840,4369,8738,17652,43690}=false := by
  apply exclude 3 _ [{15,4369,8738,17652,44970},{15,4369,12066,17652,43690},{3840,4383,8738,17652,43690}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded187,excluded193,excluded197⟩

theorem excluded198 : search 5 {240,3840,4383,8738,17476,43690}=false := by
  apply exclude 3 _ [{240,3840,4383,8738,61166},{240,3840,4383,26214,43690},{240,4383,8738,17476,44970},{240,4383,8738,20292,43690},{240,4383,12066,17476,43690},{3840,4383,8738,17652,43690}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded179,excluded185,excluded189,excluded191,excluded195,excluded197⟩

theorem excluded171 : search 6 {15,240,3840,4369,8738,17476,43690}=false := by
  apply exclude 4 _ [{15,240,3840,4369,8738,61166},{15,240,3840,4369,26214,43690},{15,240,4369,8738,17476,44970},{15,240,4369,8738,20292,43690},{15,240,4369,12066,17476,43690},{15,3840,4369,8738,17652,43690},{240,3840,4383,8738,17476,43690}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded172,excluded180,excluded186,excluded190,excluded192,excluded196,excluded198⟩

theorem excluded202 : search 3 {4383,8738,17652,53196}=false := by decide +kernel

theorem excluded201 : search 4 {15,4369,8738,17652,53196}=false := by
  apply exclude 2 _ [{4383,8738,17652,53196}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded202

theorem excluded203 : search 4 {240,4383,8738,17476,53196}=false := by
  apply exclude 2 _ [{4383,8738,17652,53196}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded202

theorem excluded200 : search 5 {15,240,4369,8738,17476,53196}=false := by
  apply exclude 3 _ [{15,4369,8738,17652,53196},{240,4383,8738,17476,53196}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded201,excluded203⟩

theorem excluded206 : search 3 {4383,8738,20292,52476}=false := by decide +kernel

theorem excluded205 : search 4 {15,4369,8738,20292,52476}=false := by
  apply exclude 2 _ [{4383,8738,20292,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded206

theorem excluded207 : search 4 {240,4383,8738,20292,52428}=false := by
  apply exclude 2 _ [{240,4383,8738,53196},{4383,8738,20292,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded3,excluded206⟩

theorem excluded204 : search 5 {15,240,4369,8738,20292,52428}=false := by
  apply exclude 3 _ [{15,240,4369,8738,53196},{15,4369,8738,20292,52476},{240,4383,8738,20292,52428}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded2,excluded205,excluded207⟩

theorem excluded209 : search 4 {240,4383,12066,17476,52428}=false := by
  apply exclude 2 _ [] (by decide) (by decide +kernel)
  simp

theorem excluded208 : search 5 {15,240,4369,12066,17476,52428}=false := by
  apply exclude 3 _ [{240,4383,12066,17476,52428}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded209

theorem excluded211 : search 4 {3840,4383,8738,17476,52476}=false := by
  apply exclude 2 _ [{4383,8738,20292,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded206

theorem excluded210 : search 5 {15,3840,4369,8738,17476,52476}=false := by
  apply exclude 3 _ [{15,4369,8738,20292,52476},{3840,4383,8738,17476,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded205,excluded211⟩

theorem excluded213 : search 4 {3840,4383,8738,17652,52428}=false := by
  apply exclude 2 _ [{3840,4383,8738,52476},{4383,8738,17652,53196}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded7,excluded202⟩

theorem excluded212 : search 5 {15,3840,4369,8738,17652,52428}=false := by
  apply exclude 3 _ [{15,3840,4369,8738,52476},{15,4369,8738,17652,53196},{3840,4383,8738,17652,52428}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded6,excluded201,excluded213⟩

theorem excluded214 : search 5 {240,3840,4383,8738,17476,52428}=false := by
  apply exclude 3 _ [{240,4383,8738,17476,53196},{240,4383,8738,20292,52428},{240,4383,12066,17476,52428},{3840,4383,8738,17476,52476},{3840,4383,8738,17652,52428}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded203,excluded207,excluded209,excluded211,excluded213⟩

theorem excluded199 : search 6 {15,240,3840,4369,8738,17476,52428}=false := by
  apply exclude 4 _ [{15,240,4369,8738,17476,53196},{15,240,4369,8738,20292,52428},{15,240,4369,12066,17476,52428},{15,3840,4369,8738,17476,52476},{15,3840,4369,8738,17652,52428},{240,3840,4383,8738,17476,52428}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded200,excluded204,excluded208,excluded210,excluded212,excluded214⟩

theorem excluded217 : search 4 {240,4383,8738,17652,36744}=false := by
  apply exclude 2 _ [{240,4383,8738,53244},{4383,8738,17652,36856}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded134,excluded143⟩

theorem excluded216 : search 5 {15,240,4369,8738,17652,36744}=false := by
  apply exclude 3 _ [{15,240,4369,8738,53244},{15,4369,8738,17652,36856},{240,4383,8738,17652,36744}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded133,excluded142,excluded217⟩

theorem excluded219 : search 4 {240,4383,8738,20468,34952}=false := by
  apply exclude 2 _ [{240,4383,8738,53244},{4383,8738,20468,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded134,excluded147⟩

theorem excluded218 : search 5 {15,240,4369,8738,20468,34952}=false := by
  apply exclude 3 _ [{15,240,4369,8738,53244},{15,4369,8738,20468,35064},{240,4383,8738,20468,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded133,excluded146,excluded219⟩

theorem excluded221 : search 4 {240,4383,12066,17652,34952}=false := by
  apply exclude 2 _ [{240,4383,12066,52476},{4383,12066,17652,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded136,excluded151⟩

theorem excluded220 : search 5 {15,240,4369,12066,17652,34952}=false := by
  apply exclude 3 _ [{15,240,4369,12066,52476},{15,4369,12066,17652,35064},{240,4383,12066,17652,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded135,excluded150,excluded221⟩

theorem excluded223 : search 4 {15,272,8738,17652,34952}=false := by
  apply exclude 2 _ [{15,272,8738,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded138

theorem excluded224 : search 4 {4080,4383,8738,17652,34952}=false := by
  apply exclude 2 _ [{4080,4383,8738,52476},{4383,8738,17652,36856}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded139,excluded143⟩

theorem excluded222 : search 5 {15,4080,4369,8738,17652,34952}=false := by
  apply exclude 3 _ [{15,272,8738,17652,34952},{15,4080,4369,8738,52476},{15,4369,8738,17652,36856},{4080,4383,8738,17652,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded223,excluded137,excluded142,excluded224⟩

theorem excluded225 : search 5 {240,3840,4383,8738,17652,34952}=false := by
  apply exclude 3 _ [{240,3840,4383,8738,52476},{240,4383,8738,17652,36744},{240,4383,8738,20468,34952},{240,4383,12066,17652,34952},{3840,4383,8738,17652,35064},{4080,4383,8738,17652,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded140,excluded217,excluded219,excluded221,excluded154,excluded224⟩

theorem excluded215 : search 6 {15,240,3840,4369,8738,17652,34952}=false := by
  apply exclude 4 _ [{15,240,3840,4369,8738,52476},{15,240,4369,8738,17652,36744},{15,240,4369,8738,20468,34952},{15,240,4369,12066,17652,34952},{15,3840,4369,8738,17652,35064},{15,4080,4369,8738,17652,34952},{240,3840,4383,8738,17652,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded132,excluded216,excluded218,excluded220,excluded153,excluded222,excluded225⟩

theorem excluded228 : search 4 {240,4383,12066,20292,34952}=false := by
  apply exclude 2 _ [{240,4383,12066,53196}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded162

theorem excluded227 : search 5 {15,240,4369,12066,20292,34952}=false := by
  apply exclude 3 _ [{15,240,4369,12066,53196},{240,4383,12066,20292,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded161,excluded228⟩

theorem excluded230 : search 4 {3840,4383,8738,20292,35064}=false := by
  apply exclude 2 _ [] (by decide) (by decide +kernel)
  simp

theorem excluded229 : search 5 {15,3840,4369,8738,20292,35064}=false := by
  apply exclude 3 _ [{3840,4383,8738,20292,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded230

theorem excluded231 : search 5 {240,3840,4383,8738,20292,34952}=false := by
  apply exclude 3 _ [{240,3840,4383,8738,53196},{240,4383,8738,20292,36744},{240,4383,12066,20292,34952},{3840,4383,8738,20292,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded163,excluded165,excluded228,excluded230⟩

theorem excluded226 : search 6 {15,240,3840,4369,8738,20292,34952}=false := by
  apply exclude 4 _ [{15,240,3840,4369,8738,53196},{15,240,4369,8738,20292,36744},{15,240,4369,12066,20292,34952},{15,3840,4369,8738,20292,35064},{240,3840,4383,8738,20292,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded160,excluded164,excluded227,excluded229,excluded231⟩

theorem excluded234 : search 4 {240,4383,8738,26214,36744}=false := by
  apply exclude 2 _ [{240,4383,8738,61422},{240,4383,26214,44970}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded176,excluded182⟩

theorem excluded233 : search 5 {15,240,4369,8738,26214,36744}=false := by
  apply exclude 3 _ [{15,240,4369,8738,61422},{15,240,4369,26214,44970},{240,4383,8738,26214,36744}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded175,excluded181,excluded234⟩

theorem excluded237 : search 3 {4383,8738,28518,35064}=false := by decide +kernel

theorem excluded236 : search 4 {15,4369,8738,28518,35064}=false := by
  apply exclude 2 _ [{4383,8738,28518,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded237

theorem excluded238 : search 4 {240,4383,8738,28518,34952}=false := by
  apply exclude 2 _ [{240,4383,8738,61422},{240,4383,28518,43690},{4383,8738,28518,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded176,excluded184,excluded237⟩

theorem excluded235 : search 5 {15,240,4369,8738,28518,34952}=false := by
  apply exclude 3 _ [{15,240,4369,8738,61422},{15,240,4369,28518,43690},{15,4369,8738,28518,35064},{240,4383,8738,28518,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded175,excluded183,excluded236,excluded238⟩

theorem excluded241 : search 3 {4383,12066,26214,35064}=false := by decide +kernel

theorem excluded240 : search 4 {15,4369,12066,26214,35064}=false := by
  apply exclude 2 _ [{4383,12066,26214,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded241

theorem excluded242 : search 4 {240,4383,12066,26214,34952}=false := by
  apply exclude 2 _ [{240,4383,12066,61166},{240,4383,26214,44970},{4383,12066,26214,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded178,excluded182,excluded241⟩

theorem excluded239 : search 5 {15,240,4369,12066,26214,34952}=false := by
  apply exclude 3 _ [{15,240,4369,12066,61166},{15,240,4369,26214,44970},{15,4369,12066,26214,35064},{240,4383,12066,26214,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded177,excluded181,excluded240,excluded242⟩

theorem excluded244 : search 4 {3840,4383,8738,26214,35064}=false := by
  apply exclude 2 _ [{4383,8738,28518,35064},{4383,12066,26214,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded237,excluded241⟩

theorem excluded243 : search 5 {15,3840,4369,8738,26214,35064}=false := by
  apply exclude 3 _ [{15,4369,8738,28518,35064},{15,4369,12066,26214,35064},{3840,4383,8738,26214,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded236,excluded240,excluded244⟩

theorem excluded245 : search 5 {240,3840,4383,8738,26214,34952}=false := by
  apply exclude 3 _ [{240,3840,4383,8738,61166},{240,3840,4383,26214,43690},{240,4383,8738,26214,36744},{240,4383,8738,28518,34952},{240,4383,12066,26214,34952},{3840,4383,8738,26214,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded179,excluded185,excluded234,excluded238,excluded242,excluded244⟩

theorem excluded232 : search 6 {15,240,3840,4369,8738,26214,34952}=false := by
  apply exclude 4 _ [{15,240,3840,4369,8738,61166},{15,240,3840,4369,26214,43690},{15,240,4369,8738,26214,36744},{15,240,4369,8738,28518,34952},{15,240,4369,12066,26214,34952},{15,3840,4369,8738,26214,35064},{240,3840,4383,8738,26214,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded172,excluded180,excluded233,excluded235,excluded239,excluded243,excluded245⟩

theorem excluded249 : search 3 {4383,8738,35064,53196}=false := by decide +kernel

theorem excluded248 : search 4 {15,4369,8738,35064,53196}=false := by
  apply exclude 2 _ [{4383,8738,35064,53196}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded249

theorem excluded250 : search 4 {240,4383,8738,34952,53196}=false := by
  apply exclude 2 _ [{4383,8738,35064,53196}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded249

theorem excluded247 : search 5 {15,240,4369,8738,34952,53196}=false := by
  apply exclude 3 _ [{15,4369,8738,35064,53196},{240,4383,8738,34952,53196}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded248,excluded250⟩

theorem excluded253 : search 3 {4383,8738,36744,52476}=false := by decide +kernel

theorem excluded252 : search 4 {15,4369,8738,36744,52476}=false := by
  apply exclude 2 _ [{4383,8738,36744,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded253

theorem excluded254 : search 4 {240,4383,8738,36744,52428}=false := by
  apply exclude 2 _ [{240,4383,8738,53196},{4383,8738,36744,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded3,excluded253⟩

theorem excluded251 : search 5 {15,240,4369,8738,36744,52428}=false := by
  apply exclude 3 _ [{15,240,4369,8738,53196},{15,4369,8738,36744,52476},{240,4383,8738,36744,52428}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded2,excluded252,excluded254⟩

theorem excluded256 : search 4 {240,4383,12066,34952,52428}=false := by
  apply exclude 2 _ [] (by decide) (by decide +kernel)
  simp

theorem excluded255 : search 5 {15,240,4369,12066,34952,52428}=false := by
  apply exclude 3 _ [{240,4383,12066,34952,52428}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded256

theorem excluded258 : search 4 {3840,4383,8738,34952,52476}=false := by
  apply exclude 2 _ [{4383,8738,36744,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded253

theorem excluded257 : search 5 {15,3840,4369,8738,34952,52476}=false := by
  apply exclude 3 _ [{15,4369,8738,36744,52476},{3840,4383,8738,34952,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded252,excluded258⟩

theorem excluded260 : search 4 {3840,4383,8738,35064,52428}=false := by
  apply exclude 2 _ [{3840,4383,8738,52476},{4383,8738,35064,53196}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded7,excluded249⟩

theorem excluded259 : search 5 {15,3840,4369,8738,35064,52428}=false := by
  apply exclude 3 _ [{15,3840,4369,8738,52476},{15,4369,8738,35064,53196},{3840,4383,8738,35064,52428}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded6,excluded248,excluded260⟩

theorem excluded261 : search 5 {240,3840,4383,8738,34952,52428}=false := by
  apply exclude 3 _ [{240,4383,8738,34952,53196},{240,4383,8738,36744,52428},{240,4383,12066,34952,52428},{3840,4383,8738,34952,52476},{3840,4383,8738,35064,52428}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded250,excluded254,excluded256,excluded258,excluded260⟩

theorem excluded246 : search 6 {15,240,3840,4369,8738,34952,52428}=false := by
  apply exclude 4 _ [{15,240,4369,8738,34952,53196},{15,240,4369,8738,36744,52428},{15,240,4369,12066,34952,52428},{15,3840,4369,8738,34952,52476},{15,3840,4369,8738,35064,52428},{240,3840,4383,8738,34952,52428}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded247,excluded251,excluded255,excluded257,excluded259,excluded261⟩

theorem excluded265 : search 3 {12,240,4383,12066}=false := by decide +kernel

theorem excluded266 : search 3 {15,240,4369,12078}=false := by decide +kernel

theorem excluded267 : search 3 {15,252,4369,12066}=false := by decide +kernel

theorem excluded264 : search 4 {12,15,240,4369,12066}=false := by
  apply exclude 2 _ [{12,240,4383,12066},{15,240,4369,12078},{15,252,4369,12066}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded265,excluded266,excluded267⟩

theorem excluded269 : search 3 {240,3840,4383,8750}=false := by decide +kernel

theorem excluded270 : search 3 {240,3852,4383,8738}=false := by decide +kernel

theorem excluded271 : search 3 {252,3840,4383,8738}=false := by decide +kernel

theorem excluded268 : search 4 {12,240,3840,4383,8738}=false := by
  apply exclude 2 _ [{12,240,4383,12066},{240,3840,4383,8750},{240,3852,4383,8738},{252,3840,4383,8738}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded265,excluded269,excluded270,excluded271⟩

theorem excluded272 : search 4 {15,240,3840,4369,8750}=false := by
  apply exclude 2 _ [{15,240,4369,12078},{240,3840,4383,8750}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded266,excluded269⟩

theorem excluded273 : search 4 {15,240,3852,4369,8738}=false := by
  apply exclude 2 _ [{15,240,4369,12078},{240,3852,4383,8738}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded266,excluded270⟩

theorem excluded274 : search 4 {15,252,3840,4369,8738}=false := by
  apply exclude 2 _ [{15,252,4369,12066},{252,3840,4383,8738}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded267,excluded271⟩

theorem excluded263 : search 5 {12,15,240,3840,4369,8738}=false := by
  apply exclude 3 _ [{12,15,240,4369,12066},{12,240,3840,4383,8738},{15,240,3840,4369,8750},{15,240,3852,4369,8738},{15,252,3840,4369,8738}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded264,excluded268,excluded272,excluded273,excluded274⟩

theorem excluded276 : search 4 {240,3840,4383,12066,52428}=false := by
  apply exclude 2 _ [{240,4383,12066,53196}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded162

theorem excluded275 : search 5 {15,240,3840,4369,12066,52428}=false := by
  apply exclude 3 _ [{15,240,4369,12066,53196},{240,3840,4383,12066,52428}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded161,excluded276⟩

theorem excluded278 : search 4 {15,240,4383,8738,53196}=false := by
  apply exclude 2 _ [] (by decide) (by decide +kernel)
  simp

theorem excluded279 : search 4 {15,240,4383,12066,52428}=false := by
  apply exclude 2 _ [{12,240,4383,12066}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded265

theorem excluded280 : search 4 {15,3840,4383,8738,52476}=false := by
  apply exclude 2 _ [] (by decide) (by decide +kernel)
  simp

theorem excluded277 : search 5 {15,240,3840,4383,8738,52428}=false := by
  apply exclude 3 _ [{12,240,3840,4383,8738},{15,240,4383,8738,53196},{15,240,4383,12066,52428},{15,3840,4383,8738,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded268,excluded278,excluded279,excluded280⟩

theorem excluded282 : search 4 {15,240,272,8738,52428}=false := by
  apply exclude 2 _ [{15,272,8738,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded138

theorem excluded283 : search 4 {240,4080,4383,8738,52428}=false := by
  apply exclude 2 _ [{240,4383,8738,53244},{4080,4383,8738,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded134,excluded139⟩

theorem excluded281 : search 5 {15,240,4080,4369,8738,52428}=false := by
  apply exclude 3 _ [{15,240,272,8738,52428},{15,240,4369,8738,53244},{15,4080,4369,8738,52476},{240,4080,4383,8738,52428}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded282,excluded133,excluded137,excluded283⟩

theorem excluded286 : search 3 {4383,8738,12066,52476}=false := by decide +kernel

theorem excluded285 : search 4 {15,4369,8738,12066,52476}=false := by
  apply exclude 2 _ [{4383,8738,12066,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded286

theorem excluded287 : search 4 {240,4383,8738,12066,52428}=false := by
  apply exclude 2 _ [{240,4383,8738,61422},{240,4383,12066,61166},{4383,8738,12066,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded176,excluded178,excluded286⟩

theorem excluded284 : search 5 {15,240,4369,8738,12066,52428}=false := by
  apply exclude 3 _ [{15,240,4369,8738,61422},{15,240,4369,12066,61166},{15,4369,8738,12066,52476},{240,4383,8738,12066,52428}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded175,excluded177,excluded285,excluded287⟩

theorem excluded290 : search 3 {4383,8738,52476,53196}=false := by decide +kernel

theorem excluded289 : search 4 {15,4369,8738,52476,53196}=false := by
  apply exclude 2 _ [{4383,8738,52476,53196}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded290

theorem excluded291 : search 4 {240,4383,8738,52428,53196}=false := by
  apply exclude 2 _ [{4383,8738,52476,53196}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded290

theorem excluded288 : search 5 {15,240,4369,8738,52428,53196}=false := by
  apply exclude 3 _ [{15,4369,8738,52476,53196},{240,4383,8738,52428,53196}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded289,excluded291⟩

theorem excluded293 : search 4 {240,4369,4383,8738,53196}=false := by
  apply exclude 2 _ [] (by decide) (by decide +kernel)
  simp

theorem excluded295 : search 3 {240,268,4383,8738}=false := by decide +kernel

theorem excluded294 : search 4 {240,4383,8738,53196}=false := by
  apply exclude 2 _ [{240,268,4383,8738},{240,4383,8738,53244},{240,4383,8738,61422}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded295,excluded134,excluded176⟩

theorem excluded292 : search 5 {15,240,4369,8738,53196}=false := by
  apply exclude 3 _ [{15,240,4369,8738,53244},{15,240,4369,8738,61422},{15,240,4383,8738,53196},{240,4369,4383,8738,53196},{240,4383,8738,53196}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded133,excluded175,excluded278,excluded293,excluded294⟩

theorem excluded298 : search 3 {240,4383,12066,61422}=false := by decide +kernel

theorem excluded297 : search 4 {15,240,4369,12066,61422}=false := by
  apply exclude 2 _ [{14,240,4369,12066},{240,4383,12066,61422}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded174,excluded298⟩

theorem excluded299 : search 4 {240,4369,4383,12066,52428}=false := by
  apply exclude 2 _ [] (by decide) (by decide +kernel)
  simp

theorem excluded300 : search 4 {240,4383,12066,52428}=false := by
  apply exclude 2 _ [{12,240,4383,12066},{240,4383,12066,52476},{240,4383,12066,61422}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded265,excluded136,excluded298⟩

theorem excluded296 : search 5 {15,240,4369,12066,52428}=false := by
  apply exclude 3 _ [{12,15,240,4369,12066},{15,240,4369,12066,52476},{15,240,4369,12066,61422},{15,240,4383,12066,52428},{240,4369,4383,12066,52428},{240,4383,12066,52428}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded264,excluded135,excluded297,excluded279,excluded299,excluded300⟩

theorem excluded302 : search 4 {3840,4383,8738,52428,52476}=false := by
  apply exclude 2 _ [{4383,8738,52476,53196}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded290

theorem excluded301 : search 5 {15,3840,4369,8738,52428,52476}=false := by
  apply exclude 3 _ [{15,4369,8738,52476,53196},{3840,4383,8738,52428,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded289,excluded302⟩

theorem excluded305 : search 3 {4383,8738,52476,53244}=false := by decide +kernel

theorem excluded304 : search 4 {15,4369,8738,52476,53244}=false := by
  apply exclude 2 _ [{15,272,8738,52476},{4383,8738,52476,53244}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded138,excluded305⟩

theorem excluded306 : search 4 {3840,4369,4383,8738,52476}=false := by
  apply exclude 2 _ [{256,4383,8738,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded102

theorem excluded307 : search 4 {3840,4383,8738,52476}=false := by
  apply exclude 2 _ [{256,4383,8738,52476},{4383,8738,12066,52476},{4383,8738,52476,53244}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded102,excluded286,excluded305⟩

theorem excluded303 : search 5 {15,3840,4369,8738,52476}=false := by
  apply exclude 3 _ [{15,256,4369,8738,52476},{15,3840,4383,8738,52476},{15,4369,8738,12066,52476},{15,4369,8738,52476,53244},{3840,4369,4383,8738,52476},{3840,4383,8738,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded101,excluded280,excluded285,excluded304,excluded306,excluded307⟩

theorem excluded308 : search 5 {240,3840,4369,4383,8738,52428}=false := by
  apply exclude 3 _ [{240,256,4383,8738,52428},{240,4369,4383,8738,53196},{240,4369,4383,12066,52428},{3840,4369,4383,8738,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded105,excluded293,excluded299,excluded306⟩

theorem excluded309 : search 5 {240,3840,4383,8738,52428}=false := by
  apply exclude 3 _ [{12,240,3840,4383,8738},{240,256,4383,8738,52428},{240,3840,4383,8738,52476},{240,3840,4383,8738,53196},{240,3840,4383,8738,61166},{240,3840,4383,12066,52428},{240,4080,4383,8738,52428},{240,4383,8738,12066,52428},{240,4383,8738,52428,53196},{240,4383,8738,53196},{240,4383,12066,52428},{3840,4383,8738,52428,52476},{3840,4383,8738,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded268,excluded105,excluded140,excluded163,excluded179,excluded276,excluded283,excluded287,excluded291,excluded294,excluded300,excluded302,excluded307⟩

theorem excluded262 : search 6 {15,240,3840,4369,8738,52428}=false := by
  apply exclude 4 _ [{12,15,240,3840,4369,8738},{15,240,256,4369,8738,52428},{15,240,3840,4369,8738,52476},{15,240,3840,4369,8738,53196},{15,240,3840,4369,8738,61166},{15,240,3840,4369,12066,52428},{15,240,3840,4383,8738,52428},{15,240,4080,4369,8738,52428},{15,240,4369,8738,12066,52428},{15,240,4369,8738,52428,53196},{15,240,4369,8738,53196},{15,240,4369,12066,52428},{15,3840,4369,8738,52428,52476},{15,3840,4369,8738,52476},{240,3840,4369,4383,8738,52428},{240,3840,4383,8738,52428}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded263,excluded94,excluded132,excluded160,excluded172,excluded275,excluded277,excluded281,excluded284,excluded288,excluded292,excluded296,excluded301,excluded303,excluded308,excluded309⟩

theorem excluded311 : search 5 {240,3840,4383,12066,17476,34952}=false := by
  apply exclude 3 _ [{240,3840,4383,12066,52428},{240,4383,12066,17476,36744},{240,4383,12066,20292,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded276,excluded167,excluded228⟩

theorem excluded310 : search 6 {15,240,3840,4369,12066,17476,34952}=false := by
  apply exclude 4 _ [{15,240,3840,4369,12066,52428},{15,240,4369,12066,17476,36744},{15,240,4369,12066,20292,34952},{240,3840,4383,12066,17476,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded275,excluded166,excluded227,excluded311⟩

theorem excluded314 : search 4 {15,4383,8738,17652,36744}=false := by
  apply exclude 2 _ [] (by decide) (by decide +kernel)
  simp

theorem excluded313 : search 5 {15,240,4383,8738,17476,36744}=false := by
  apply exclude 3 _ [{4,240,4383,8738,36744},{15,240,4383,8738,53196},{15,4383,8738,17652,36744}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded27,excluded278,excluded314⟩

theorem excluded316 : search 4 {15,4383,8738,20292,35064}=false := by
  apply exclude 2 _ [] (by decide) (by decide +kernel)
  simp

theorem excluded315 : search 5 {15,240,4383,8738,20292,34952}=false := by
  apply exclude 3 _ [{8,240,4383,8738,20292},{15,240,4383,8738,53196},{15,4383,8738,20292,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded61,excluded278,excluded316⟩

theorem excluded317 : search 5 {15,240,4383,12066,17476,34952}=false := by
  apply exclude 3 _ [{4,240,4383,12066,34952},{8,240,4383,12066,17476},{15,240,4383,12066,52428}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded35,excluded69,excluded279⟩

theorem excluded318 : search 5 {15,3840,4383,8738,17476,35064}=false := by
  apply exclude 3 _ [{4,3840,4383,8738,35064},{15,3840,4383,8738,52476},{15,4383,8738,20292,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded43,excluded280,excluded316⟩

theorem excluded319 : search 5 {15,3840,4383,8738,17652,34952}=false := by
  apply exclude 3 _ [{8,3840,4383,8738,17652},{15,3840,4383,8738,52476},{15,4383,8738,17652,36744}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded77,excluded280,excluded314⟩

theorem excluded312 : search 6 {15,240,3840,4383,8738,17476,34952}=false := by
  apply exclude 4 _ [{4,240,3840,4383,8738,34952},{8,240,3840,4383,8738,17476},{15,240,3840,4383,8738,52428},{15,240,4383,8738,17476,36744},{15,240,4383,8738,20292,34952},{15,240,4383,12066,17476,34952},{15,3840,4383,8738,17476,35064},{15,3840,4383,8738,17652,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded50,excluded84,excluded277,excluded313,excluded315,excluded317,excluded318,excluded319⟩

theorem excluded321 : search 5 {15,240,272,8738,17476,34952}=false := by
  apply exclude 3 _ [{15,240,272,8738,52428},{15,272,8738,17476,35064},{15,272,8738,17652,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded282,excluded156,excluded223⟩

theorem excluded322 : search 5 {240,4080,4383,8738,17476,34952}=false := by
  apply exclude 3 _ [{240,4080,4383,8738,52428},{240,4383,8738,17476,36856},{240,4383,8738,20468,34952},{4080,4383,8738,17476,35064},{4080,4383,8738,17652,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded283,excluded144,excluded219,excluded157,excluded224⟩

theorem excluded320 : search 6 {15,240,4080,4369,8738,17476,34952}=false := by
  apply exclude 4 _ [{15,240,272,8738,17476,34952},{15,240,4080,4369,8738,52428},{15,240,4369,8738,17476,36856},{15,240,4369,8738,20468,34952},{15,4080,4369,8738,17476,35064},{15,4080,4369,8738,17652,34952},{240,4080,4383,8738,17476,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded321,excluded281,excluded141,excluded218,excluded155,excluded222,excluded322⟩

theorem excluded325 : search 4 {4383,8738,12066,17476,35064}=false := by
  apply exclude 2 _ [{4383,8738,12066,52476},{4383,8738,28518,35064},{4383,12066,26214,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded286,excluded237,excluded241⟩

theorem excluded324 : search 5 {15,4369,8738,12066,17476,35064}=false := by
  apply exclude 3 _ [{15,4369,8738,12066,52476},{15,4369,8738,28518,35064},{15,4369,12066,26214,35064},{4383,8738,12066,17476,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded285,excluded236,excluded240,excluded325⟩

theorem excluded327 : search 4 {4383,8738,12066,17652,34952}=false := by
  apply exclude 2 _ [{4383,8738,12066,52476},{4383,8738,17652,44970},{4383,12066,17652,43690}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded286,excluded188,excluded194⟩

theorem excluded326 : search 5 {15,4369,8738,12066,17652,34952}=false := by
  apply exclude 3 _ [{15,4369,8738,12066,52476},{15,4369,8738,17652,44970},{15,4369,12066,17652,43690},{4383,8738,12066,17652,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded285,excluded187,excluded193,excluded327⟩

theorem excluded328 : search 5 {240,4383,8738,12066,17476,34952}=false := by
  apply exclude 3 _ [{240,4383,8738,12066,52428},{240,4383,8738,17476,44970},{240,4383,8738,28518,34952},{240,4383,12066,17476,43690},{240,4383,12066,26214,34952},{4383,8738,12066,17476,35064},{4383,8738,12066,17652,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded287,excluded189,excluded238,excluded195,excluded242,excluded325,excluded327⟩

theorem excluded323 : search 6 {15,240,4369,8738,12066,17476,34952}=false := by
  apply exclude 4 _ [{15,240,4369,8738,12066,52428},{15,240,4369,8738,17476,44970},{15,240,4369,8738,28518,34952},{15,240,4369,12066,17476,43690},{15,240,4369,12066,26214,34952},{15,4369,8738,12066,17476,35064},{15,4369,8738,12066,17652,34952},{240,4383,8738,12066,17476,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded284,excluded186,excluded235,excluded192,excluded239,excluded324,excluded326,excluded328⟩

theorem excluded331 : search 4 {4383,8738,17476,20292,35064}=false := by
  apply exclude 2 _ [{4383,8738,20292,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded206

theorem excluded330 : search 5 {15,4369,8738,17476,20292,35064}=false := by
  apply exclude 3 _ [{15,4369,8738,20292,52476},{4383,8738,17476,20292,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded205,excluded331⟩

theorem excluded333 : search 4 {4383,8738,17652,20292,34952}=false := by
  apply exclude 2 _ [{4383,8738,17652,53196},{4383,8738,20292,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded202,excluded206⟩

theorem excluded332 : search 5 {15,4369,8738,17652,20292,34952}=false := by
  apply exclude 3 _ [{15,4369,8738,17652,53196},{15,4369,8738,20292,52476},{4383,8738,17652,20292,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded201,excluded205,excluded333⟩

theorem excluded334 : search 5 {240,4383,8738,17476,20292,34952}=false := by
  apply exclude 3 _ [{240,4383,8738,17476,53196},{240,4383,8738,20292,52428},{4383,8738,17476,20292,35064},{4383,8738,17652,20292,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded203,excluded207,excluded331,excluded333⟩

theorem excluded329 : search 6 {15,240,4369,8738,17476,20292,34952}=false := by
  apply exclude 4 _ [{15,240,4369,8738,17476,53196},{15,240,4369,8738,20292,52428},{15,4369,8738,17476,20292,35064},{15,4369,8738,17652,20292,34952},{240,4383,8738,17476,20292,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded200,excluded204,excluded330,excluded332,excluded334⟩

theorem excluded337 : search 4 {4383,8738,17476,35064,36744}=false := by
  apply exclude 2 _ [{4383,8738,35064,53196},{4383,8738,36744,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded249,excluded253⟩

theorem excluded336 : search 5 {15,4369,8738,17476,35064,36744}=false := by
  apply exclude 3 _ [{15,4369,8738,35064,53196},{15,4369,8738,36744,52476},{4383,8738,17476,35064,36744}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded248,excluded252,excluded337⟩

theorem excluded339 : search 4 {4383,8738,17652,34952,36744}=false := by
  apply exclude 2 _ [{4383,8738,36744,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded253

theorem excluded338 : search 5 {15,4369,8738,17652,34952,36744}=false := by
  apply exclude 3 _ [{15,4369,8738,36744,52476},{4383,8738,17652,34952,36744}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded252,excluded339⟩

theorem excluded340 : search 5 {240,4383,8738,17476,34952,36744}=false := by
  apply exclude 3 _ [{240,4383,8738,34952,53196},{240,4383,8738,36744,52428},{4383,8738,17476,35064,36744},{4383,8738,17652,34952,36744}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded250,excluded254,excluded337,excluded339⟩

theorem excluded335 : search 6 {15,240,4369,8738,17476,34952,36744}=false := by
  apply exclude 4 _ [{15,240,4369,8738,34952,53196},{15,240,4369,8738,36744,52428},{15,4369,8738,17476,35064,36744},{15,4369,8738,17652,34952,36744},{240,4383,8738,17476,34952,36744}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded247,excluded251,excluded336,excluded338,excluded340⟩

theorem excluded343 : search 4 {240,4383,8738,36744,53196}=false := by
  apply exclude 2 _ [] (by decide) (by decide +kernel)
  simp

theorem excluded342 : search 5 {15,240,4369,8738,36744,53196}=false := by
  apply exclude 3 _ [{240,4383,8738,36744,53196}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded343

theorem excluded345 : search 4 {4383,8738,17476,17652,36744}=false := by
  apply exclude 2 _ [{4383,8738,17652,53196}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded202

theorem excluded344 : search 5 {15,4369,8738,17476,17652,36744}=false := by
  apply exclude 3 _ [{15,4369,8738,17652,53196},{4383,8738,17476,17652,36744}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded201,excluded345⟩

theorem excluded348 : search 3 {4383,8738,17652,53244}=false := by decide +kernel

theorem excluded347 : search 4 {15,4369,8738,17652,53244}=false := by
  apply exclude 2 _ [{4383,8738,17652,53244}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded348

theorem excluded349 : search 4 {4369,4383,8738,17652,36744}=false := by
  apply exclude 2 _ [] (by decide) (by decide +kernel)
  simp

theorem excluded351 : search 3 {264,4383,8738,17652}=false := by decide +kernel

theorem excluded350 : search 4 {4383,8738,17652,36744}=false := by
  apply exclude 2 _ [{264,4383,8738,17652},{4383,8738,17652,44970},{4383,8738,17652,53244}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded351,excluded188,excluded348⟩

theorem excluded346 : search 5 {15,4369,8738,17652,36744}=false := by
  apply exclude 3 _ [{15,4369,8738,17652,44970},{15,4369,8738,17652,53244},{15,4383,8738,17652,36744},{4369,4383,8738,17652,36744},{4383,8738,17652,36744}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded187,excluded347,excluded314,excluded349,excluded350⟩

theorem excluded352 : search 5 {240,4369,4383,8738,17476,36744}=false := by
  apply exclude 3 _ [{240,4369,4383,8738,53196},{4369,4383,8738,17652,36744}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded293,excluded349⟩

theorem excluded355 : search 3 {240,4383,8738,17740}=false := by decide +kernel

theorem excluded356 : search 3 {240,4383,9002,17476}=false := by decide +kernel

theorem excluded357 : search 3 {504,4383,8738,17476}=false := by decide +kernel

theorem excluded354 : search 4 {240,264,4383,8738,17476}=false := by
  apply exclude 2 _ [{240,4383,8738,17740},{240,4383,9002,17476},{264,4383,8738,17652},{504,4383,8738,17476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded355,excluded356,excluded351,excluded357⟩

theorem excluded353 : search 5 {240,4383,8738,17476,36744}=false := by
  apply exclude 3 _ [{4,240,4383,8738,36744},{240,264,4383,8738,17476},{240,4383,8738,17476,36856},{240,4383,8738,17476,44970},{240,4383,8738,17476,53196},{240,4383,8738,17652,36744},{240,4383,8738,26214,36744},{240,4383,8738,36744,53196},{240,4383,8738,53196},{4383,8738,17476,17652,36744},{4383,8738,17652,36744}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded27,excluded354,excluded144,excluded189,excluded203,excluded217,excluded234,excluded343,excluded294,excluded345,excluded350⟩

theorem excluded341 : search 6 {15,240,4369,8738,17476,36744}=false := by
  apply exclude 4 _ [{4,15,240,4369,8738,36744},{15,240,4369,8738,17476,36856},{15,240,4369,8738,17476,44970},{15,240,4369,8738,17476,53196},{15,240,4369,8738,17652,36744},{15,240,4369,8738,26214,36744},{15,240,4369,8738,36744,53196},{15,240,4369,8738,53196},{15,240,4383,8738,17476,36744},{15,4369,8738,17476,17652,36744},{15,4369,8738,17652,36744},{240,4369,4383,8738,17476,36744},{240,4383,8738,17476,36744}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded26,excluded141,excluded186,excluded200,excluded216,excluded233,excluded342,excluded292,excluded313,excluded344,excluded346,excluded352,excluded353⟩

theorem excluded360 : search 4 {240,4383,8738,20292,53196}=false := by
  apply exclude 2 _ [] (by decide) (by decide +kernel)
  simp

theorem excluded359 : search 5 {15,240,4369,8738,20292,53196}=false := by
  apply exclude 3 _ [{240,4383,8738,20292,53196}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded360

theorem excluded362 : search 4 {4383,8738,20292,34952,35064}=false := by
  apply exclude 2 _ [{4383,8738,35064,53196}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded249

theorem excluded361 : search 5 {15,4369,8738,20292,34952,35064}=false := by
  apply exclude 3 _ [{15,4369,8738,35064,53196},{4383,8738,20292,34952,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded248,excluded362⟩

theorem excluded365 : search 3 {4383,8738,35064,53244}=false := by decide +kernel

theorem excluded364 : search 4 {15,4369,8738,35064,53244}=false := by
  apply exclude 2 _ [{4383,8738,35064,53244}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded365

theorem excluded366 : search 4 {4369,4383,8738,20292,35064}=false := by
  apply exclude 2 _ [] (by decide) (by decide +kernel)
  simp

theorem excluded368 : search 3 {260,4383,8738,35064}=false := by decide +kernel

theorem excluded367 : search 4 {4383,8738,20292,35064}=false := by
  apply exclude 2 _ [{260,4383,8738,35064},{4383,8738,28518,35064},{4383,8738,35064,53244}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded368,excluded237,excluded365⟩

theorem excluded363 : search 5 {15,4369,8738,20292,35064}=false := by
  apply exclude 3 _ [{15,4369,8738,28518,35064},{15,4369,8738,35064,53244},{15,4383,8738,20292,35064},{4369,4383,8738,20292,35064},{4383,8738,20292,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded236,excluded364,excluded316,excluded366,excluded367⟩

theorem excluded369 : search 5 {240,4369,4383,8738,20292,34952}=false := by
  apply exclude 3 _ [{240,4369,4383,8738,53196},{4369,4383,8738,20292,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded293,excluded366⟩

theorem excluded372 : search 3 {240,4383,8738,35212}=false := by decide +kernel

theorem excluded373 : search 3 {240,4383,8998,34952}=false := by decide +kernel

theorem excluded374 : search 3 {500,4383,8738,34952}=false := by decide +kernel

theorem excluded371 : search 4 {240,260,4383,8738,34952}=false := by
  apply exclude 2 _ [{240,4383,8738,35212},{240,4383,8998,34952},{260,4383,8738,35064},{500,4383,8738,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded372,excluded373,excluded368,excluded374⟩

theorem excluded370 : search 5 {240,4383,8738,20292,34952}=false := by
  apply exclude 3 _ [{8,240,4383,8738,20292},{240,260,4383,8738,34952},{240,4383,8738,20292,35064},{240,4383,8738,20292,43690},{240,4383,8738,20292,53196},{240,4383,8738,20468,34952},{240,4383,8738,28518,34952},{240,4383,8738,34952,53196},{240,4383,8738,53196},{4383,8738,20292,34952,35064},{4383,8738,20292,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded61,excluded371,excluded148,excluded191,excluded360,excluded219,excluded238,excluded250,excluded294,excluded362,excluded367⟩

theorem excluded358 : search 6 {15,240,4369,8738,20292,34952}=false := by
  apply exclude 4 _ [{8,15,240,4369,8738,20292},{15,240,4369,8738,20292,35064},{15,240,4369,8738,20292,43690},{15,240,4369,8738,20292,53196},{15,240,4369,8738,20468,34952},{15,240,4369,8738,28518,34952},{15,240,4369,8738,34952,53196},{15,240,4369,8738,53196},{15,240,4383,8738,20292,34952},{15,4369,8738,20292,34952,35064},{15,4369,8738,20292,35064},{240,4369,4383,8738,20292,34952},{240,4383,8738,20292,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded60,excluded145,excluded190,excluded359,excluded218,excluded235,excluded247,excluded292,excluded315,excluded361,excluded363,excluded369,excluded370⟩

theorem excluded378 : search 3 {240,4383,28518,44970}=false := by decide +kernel

theorem excluded377 : search 4 {15,240,4369,28518,44970}=false := by
  apply exclude 2 _ [{240,4383,28518,44970}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded378

theorem excluded379 : search 4 {240,4383,12066,17476,44970}=false := by
  apply exclude 2 _ [{240,4383,12066,61422},{240,4383,28518,44970}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded298,excluded378⟩

theorem excluded376 : search 5 {15,240,4369,12066,17476,44970}=false := by
  apply exclude 3 _ [{15,240,4369,12066,61422},{15,240,4369,28518,44970},{240,4383,12066,17476,44970}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded297,excluded377,excluded379⟩

theorem excluded381 : search 4 {240,4383,12066,28518,34952}=false := by
  apply exclude 2 _ [{240,4383,12066,61422},{240,4383,28518,44970}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded298,excluded378⟩

theorem excluded380 : search 5 {15,240,4369,12066,28518,34952}=false := by
  apply exclude 3 _ [{15,240,4369,12066,61422},{15,240,4369,28518,44970},{240,4383,12066,28518,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded297,excluded377,excluded381⟩

theorem excluded382 : search 5 {240,4369,4383,12066,17476,34952}=false := by
  apply exclude 3 _ [{240,4369,4383,12066,52428}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded299

theorem excluded383 : search 5 {240,4383,12066,17476,34952}=false := by
  apply exclude 3 _ [{4,240,4383,12066,34952},{8,240,4383,12066,17476},{240,4383,12066,17476,35064},{240,4383,12066,17476,44970},{240,4383,12066,17476,52428},{240,4383,12066,17652,34952},{240,4383,12066,28518,34952},{240,4383,12066,34952,52428},{240,4383,12066,52428}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded35,excluded69,excluded152,excluded379,excluded209,excluded221,excluded381,excluded256,excluded300⟩

theorem excluded375 : search 6 {15,240,4369,12066,17476,34952}=false := by
  apply exclude 4 _ [{4,15,240,4369,12066,34952},{8,15,240,4369,12066,17476},{15,240,4369,12066,17476,35064},{15,240,4369,12066,17476,44970},{15,240,4369,12066,17476,52428},{15,240,4369,12066,17652,34952},{15,240,4369,12066,28518,34952},{15,240,4369,12066,34952,52428},{15,240,4369,12066,52428},{15,240,4383,12066,17476,34952},{240,4369,4383,12066,17476,34952},{240,4383,12066,17476,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded34,excluded68,excluded149,excluded376,excluded208,excluded220,excluded380,excluded255,excluded296,excluded317,excluded382,excluded383⟩

theorem excluded385 : search 5 {3840,4383,8738,17476,17652,34952}=false := by
  apply exclude 3 _ [{3840,4383,8738,17476,52476},{3840,4383,8738,17652,52428},{4383,8738,17476,17652,36744},{4383,8738,17652,20292,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded211,excluded213,excluded345,excluded333⟩

theorem excluded384 : search 6 {15,3840,4369,8738,17476,17652,34952}=false := by
  apply exclude 4 _ [{15,3840,4369,8738,17476,52476},{15,3840,4369,8738,17652,52428},{15,4369,8738,17476,17652,36744},{15,4369,8738,17652,20292,34952},{3840,4383,8738,17476,17652,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded210,excluded212,excluded344,excluded332,excluded385⟩

theorem excluded387 : search 5 {3840,4383,8738,17476,34952,35064}=false := by
  apply exclude 3 _ [{3840,4383,8738,34952,52476},{3840,4383,8738,35064,52428},{4383,8738,17476,35064,36744},{4383,8738,20292,34952,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded258,excluded260,excluded337,excluded362⟩

theorem excluded386 : search 6 {15,3840,4369,8738,17476,34952,35064}=false := by
  apply exclude 4 _ [{15,3840,4369,8738,34952,52476},{15,3840,4369,8738,35064,52428},{15,4369,8738,17476,35064,36744},{15,4369,8738,20292,34952,35064},{3840,4383,8738,17476,34952,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded257,excluded259,excluded336,excluded361,excluded387⟩

theorem excluded391 : search 3 {4383,8738,36856,52476}=false := by decide +kernel

theorem excluded390 : search 4 {15,4369,8738,36856,52476}=false := by
  apply exclude 2 _ [{15,272,8738,52476},{4383,8738,36856,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded138,excluded391⟩

theorem excluded392 : search 4 {3840,4383,8738,35064,52476}=false := by
  apply exclude 2 _ [{4383,8738,35064,53244},{4383,8738,36856,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded365,excluded391⟩

theorem excluded389 : search 5 {15,3840,4369,8738,35064,52476}=false := by
  apply exclude 3 _ [{15,4369,8738,35064,53244},{15,4369,8738,36856,52476},{3840,4383,8738,35064,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded364,excluded390,excluded392⟩

theorem excluded394 : search 4 {4383,8738,17476,35064,36856}=false := by
  apply exclude 2 _ [{4383,8738,35064,53244},{4383,8738,36856,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded365,excluded391⟩

theorem excluded393 : search 5 {15,4369,8738,17476,35064,36856}=false := by
  apply exclude 3 _ [{15,272,8738,17476,35064},{15,4369,8738,35064,53244},{15,4369,8738,36856,52476},{4383,8738,17476,35064,36856}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded156,excluded364,excluded390,excluded394⟩

theorem excluded395 : search 5 {3840,4369,4383,8738,17476,35064}=false := by
  apply exclude 3 _ [{256,4383,8738,17476,35064},{3840,4369,4383,8738,52476},{4369,4383,8738,20292,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded125,excluded306,excluded366⟩

theorem excluded396 : search 5 {3840,4383,8738,17476,35064}=false := by
  apply exclude 3 _ [{4,3840,4383,8738,35064},{256,4383,8738,17476,35064},{3840,4383,8738,17476,52476},{3840,4383,8738,20292,35064},{3840,4383,8738,26214,35064},{3840,4383,8738,35064,52476},{3840,4383,8738,52476},{4383,8738,12066,17476,35064},{4383,8738,17476,20292,35064},{4383,8738,17476,35064,36856},{4383,8738,20292,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded43,excluded125,excluded211,excluded230,excluded244,excluded392,excluded307,excluded325,excluded331,excluded394,excluded367⟩

theorem excluded388 : search 6 {15,3840,4369,8738,17476,35064}=false := by
  apply exclude 4 _ [{4,15,3840,4369,8738,35064},{15,256,4369,8738,17476,35064},{15,3840,4369,8738,17476,52476},{15,3840,4369,8738,20292,35064},{15,3840,4369,8738,26214,35064},{15,3840,4369,8738,35064,52476},{15,3840,4369,8738,52476},{15,3840,4383,8738,17476,35064},{15,4369,8738,12066,17476,35064},{15,4369,8738,17476,20292,35064},{15,4369,8738,17476,35064,36856},{15,4369,8738,20292,35064},{3840,4369,4383,8738,17476,35064},{3840,4383,8738,17476,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded42,excluded124,excluded210,excluded229,excluded243,excluded389,excluded303,excluded318,excluded324,excluded330,excluded393,excluded363,excluded395,excluded396⟩

theorem excluded400 : search 3 {4383,8738,20468,52476}=false := by decide +kernel

theorem excluded399 : search 4 {15,4369,8738,20468,52476}=false := by
  apply exclude 2 _ [{15,272,8738,52476},{4383,8738,20468,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded138,excluded400⟩

theorem excluded401 : search 4 {3840,4383,8738,17652,52476}=false := by
  apply exclude 2 _ [{4383,8738,17652,53244},{4383,8738,20468,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded348,excluded400⟩

theorem excluded398 : search 5 {15,3840,4369,8738,17652,52476}=false := by
  apply exclude 3 _ [{15,4369,8738,17652,53244},{15,4369,8738,20468,52476},{3840,4383,8738,17652,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded347,excluded399,excluded401⟩

theorem excluded403 : search 4 {4383,8738,17652,20468,34952}=false := by
  apply exclude 2 _ [{4383,8738,17652,53244},{4383,8738,20468,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded348,excluded400⟩

theorem excluded402 : search 5 {15,4369,8738,17652,20468,34952}=false := by
  apply exclude 3 _ [{15,272,8738,17652,34952},{15,4369,8738,17652,53244},{15,4369,8738,20468,52476},{4383,8738,17652,20468,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded223,excluded347,excluded399,excluded403⟩

theorem excluded404 : search 5 {3840,4369,4383,8738,17652,34952}=false := by
  apply exclude 3 _ [{256,4383,8738,17652,34952},{3840,4369,4383,8738,52476},{4369,4383,8738,17652,36744}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded127,excluded306,excluded349⟩

theorem excluded405 : search 5 {3840,4383,8738,17652,34952}=false := by
  apply exclude 3 _ [{8,3840,4383,8738,17652},{256,4383,8738,17652,34952},{3840,4383,8738,17652,36744},{3840,4383,8738,17652,43690},{3840,4383,8738,17652,52476},{3840,4383,8738,34952,52476},{3840,4383,8738,52476},{4383,8738,12066,17652,34952},{4383,8738,17652,20468,34952},{4383,8738,17652,34952,36744},{4383,8738,17652,36744}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded77,excluded127,excluded169,excluded197,excluded401,excluded258,excluded307,excluded327,excluded403,excluded339,excluded350⟩

theorem excluded397 : search 6 {15,3840,4369,8738,17652,34952}=false := by
  apply exclude 4 _ [{8,15,3840,4369,8738,17652},{15,256,4369,8738,17652,34952},{15,3840,4369,8738,17652,36744},{15,3840,4369,8738,17652,43690},{15,3840,4369,8738,17652,52476},{15,3840,4369,8738,34952,52476},{15,3840,4369,8738,52476},{15,3840,4383,8738,17652,34952},{15,4369,8738,12066,17652,34952},{15,4369,8738,17652,20468,34952},{15,4369,8738,17652,34952,36744},{15,4369,8738,17652,36744},{3840,4369,4383,8738,17652,34952},{3840,4383,8738,17652,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded76,excluded126,excluded168,excluded196,excluded398,excluded257,excluded303,excluded319,excluded326,excluded402,excluded338,excluded346,excluded404,excluded405⟩

theorem excluded406 : search 6 {240,3840,4369,4383,8738,17476,34952}=false := by
  apply exclude 4 _ [{240,256,4383,8738,17476,34952},{240,3840,4369,4383,8738,52428},{240,4369,4383,8738,17476,36744},{240,4369,4383,8738,20292,34952},{240,4369,4383,12066,17476,34952},{3840,4369,4383,8738,17476,35064},{3840,4369,4383,8738,17652,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded130,excluded308,excluded352,excluded369,excluded382,excluded395,excluded404⟩

theorem excluded407 : search 6 {240,3840,4383,8738,17476,34952}=false := by
  apply exclude 4 _ [{4,240,3840,4383,8738,34952},{8,240,3840,4383,8738,17476},{240,256,4383,8738,17476,34952},{240,3840,4383,8738,17476,35064},{240,3840,4383,8738,17476,36744},{240,3840,4383,8738,17476,43690},{240,3840,4383,8738,17476,52428},{240,3840,4383,8738,17652,34952},{240,3840,4383,8738,20292,34952},{240,3840,4383,8738,26214,34952},{240,3840,4383,8738,34952,52428},{240,3840,4383,8738,52428},{240,3840,4383,12066,17476,34952},{240,4080,4383,8738,17476,34952},{240,4383,8738,12066,17476,34952},{240,4383,8738,17476,20292,34952},{240,4383,8738,17476,34952,36744},{240,4383,8738,17476,36744},{240,4383,8738,20292,34952},{240,4383,12066,17476,34952},{3840,4383,8738,17476,17652,34952},{3840,4383,8738,17476,34952,35064},{3840,4383,8738,17476,35064},{3840,4383,8738,17652,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded50,excluded84,excluded130,excluded158,excluded170,excluded198,excluded214,excluded225,excluded231,excluded245,excluded261,excluded309,excluded311,excluded322,excluded328,excluded334,excluded340,excluded353,excluded370,excluded383,excluded385,excluded387,excluded396,excluded405⟩

theorem excluded24 : search 7 {15,240,3840,4369,8738,17476,34952}=false := by
  apply exclude 5 _ [{4,15,240,3840,4369,8738,34952},{8,15,240,3840,4369,8738,17476},{15,240,256,4369,8738,17476,34952},{15,240,3840,4369,8738,17476,35064},{15,240,3840,4369,8738,17476,36744},{15,240,3840,4369,8738,17476,43690},{15,240,3840,4369,8738,17476,52428},{15,240,3840,4369,8738,17652,34952},{15,240,3840,4369,8738,20292,34952},{15,240,3840,4369,8738,26214,34952},{15,240,3840,4369,8738,34952,52428},{15,240,3840,4369,8738,52428},{15,240,3840,4369,12066,17476,34952},{15,240,3840,4383,8738,17476,34952},{15,240,4080,4369,8738,17476,34952},{15,240,4369,8738,12066,17476,34952},{15,240,4369,8738,17476,20292,34952},{15,240,4369,8738,17476,34952,36744},{15,240,4369,8738,17476,36744},{15,240,4369,8738,20292,34952},{15,240,4369,12066,17476,34952},{15,3840,4369,8738,17476,17652,34952},{15,3840,4369,8738,17476,34952,35064},{15,3840,4369,8738,17476,35064},{15,3840,4369,8738,17652,34952},{240,3840,4369,4383,8738,17476,34952},{240,3840,4383,8738,17476,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded25,excluded59,excluded93,excluded131,excluded159,excluded171,excluded199,excluded215,excluded226,excluded232,excluded246,excluded262,excluded310,excluded312,excluded320,excluded323,excluded329,excluded335,excluded341,excluded358,excluded375,excluded384,excluded386,excluded388,excluded397,excluded406,excluded407⟩

theorem excluded411 : search 4 {15,240,4369,12066,64716}=false := by
  apply exclude 2 _ [] (by decide) (by decide +kernel)
  simp

theorem excluded410 : search 5 {15,240,3840,4369,8738,64716}=false := by
  apply exclude 3 _ [{15,240,4369,12066,64716}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded411

theorem excluded412 : search 5 {15,240,4369,8738,20292,63624}=false := by
  apply exclude 3 _ [] (by decide) (by decide +kernel)
  simp

theorem excluded413 : search 5 {15,240,4369,12066,17476,63624}=false := by
  apply exclude 3 _ [{15,240,4369,12066,64716}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded411

theorem excluded414 : search 5 {15,3840,4369,8738,17652,63624}=false := by
  apply exclude 3 _ [] (by decide) (by decide +kernel)
  simp

theorem excluded409 : search 6 {15,240,3840,4369,8738,17476,63624}=false := by
  apply exclude 4 _ [{15,240,3840,4369,8738,64716},{15,240,4369,8738,20292,63624},{15,240,4369,12066,17476,63624},{15,3840,4369,8738,17652,63624}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded410,excluded412,excluded413,excluded414⟩

theorem excluded416 : search 5 {15,240,4369,8738,36744,62532}=false := by
  apply exclude 3 _ [] (by decide) (by decide +kernel)
  simp

theorem excluded417 : search 5 {15,240,4369,12066,34952,62532}=false := by
  apply exclude 3 _ [{15,240,4369,12066,64716}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded411

theorem excluded418 : search 5 {15,3840,4369,8738,35064,62532}=false := by
  apply exclude 3 _ [] (by decide) (by decide +kernel)
  simp

theorem excluded415 : search 6 {15,240,3840,4369,8738,34952,62532}=false := by
  apply exclude 4 _ [{15,240,3840,4369,8738,64716},{15,240,4369,8738,36744,62532},{15,240,4369,12066,34952,62532},{15,3840,4369,8738,35064,62532}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded410,excluded416,excluded417,excluded418⟩

theorem excluded421 : search 4 {15,240,4369,53196,61986}=false := by
  apply exclude 2 _ [] (by decide) (by decide +kernel)
  simp

theorem excluded420 : search 5 {15,240,3840,4369,52428,61986}=false := by
  apply exclude 3 _ [{15,240,4369,53196,61986}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded421

theorem excluded422 : search 5 {15,240,3840,8738,52428,61713}=false := by
  apply exclude 3 _ [] (by decide) (by decide +kernel)
  simp

theorem excluded424 : search 4 {240,4383,8738,53196,61440}=false := by
  apply exclude 2 _ [] (by decide) (by decide +kernel)
  simp

theorem excluded423 : search 5 {15,240,4369,8738,53196,61440}=false := by
  apply exclude 3 _ [{15,240,4369,53196,61986},{240,4383,8738,53196,61440}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded421,excluded424⟩

theorem excluded426 : search 4 {240,4383,12066,52428,61440}=false := by
  apply exclude 2 _ [] (by decide) (by decide +kernel)
  simp

theorem excluded425 : search 5 {15,240,4369,12066,52428,61440}=false := by
  apply exclude 3 _ [{15,240,4369,12066,64716},{240,4383,12066,52428,61440}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded411,excluded426⟩

theorem excluded428 : search 4 {3840,4383,8738,52476,61440}=false := by
  apply exclude 2 _ [] (by decide) (by decide +kernel)
  simp

theorem excluded427 : search 5 {15,3840,4369,8738,52476,61440}=false := by
  apply exclude 3 _ [{3840,4383,8738,52476,61440}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded428

theorem excluded429 : search 5 {240,3840,4383,8738,52428,61440}=false := by
  apply exclude 3 _ [{240,4383,8738,53196,61440},{240,4383,12066,52428,61440},{3840,4383,8738,52476,61440}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded424,excluded426,excluded428⟩

theorem excluded419 : search 6 {15,240,3840,4369,8738,52428,61440}=false := by
  apply exclude 4 _ [{15,240,3840,4369,8738,64716},{15,240,3840,4369,52428,61986},{15,240,3840,8738,52428,61713},{15,240,4369,8738,53196,61440},{15,240,4369,12066,52428,61440},{15,3840,4369,8738,52476,61440},{240,3840,4383,8738,52428,61440}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded410,excluded420,excluded422,excluded423,excluded425,excluded427,excluded429⟩

theorem excluded431 : search 5 {15,240,4369,17476,36744,61986}=false := by
  apply exclude 3 _ [{15,240,4369,53196,61986}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded421

theorem excluded432 : search 5 {15,240,4369,20292,34952,61986}=false := by
  apply exclude 3 _ [{15,240,4369,53196,61986}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded421

theorem excluded430 : search 6 {15,240,3840,4369,17476,34952,61986}=false := by
  apply exclude 4 _ [{15,240,3840,4369,52428,61986},{15,240,4369,17476,36744,61986},{15,240,4369,20292,34952,61986}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded420,excluded431,excluded432⟩

theorem excluded433 : search 6 {15,240,3840,8738,17476,34952,61713}=false := by
  apply exclude 4 _ [{15,240,3840,8738,52428,61713}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded422

theorem excluded436 : search 4 {4383,8738,17652,36744,61440}=false := by
  apply exclude 2 _ [] (by decide) (by decide +kernel)
  simp

theorem excluded435 : search 5 {15,4369,8738,17652,36744,61440}=false := by
  apply exclude 3 _ [{4383,8738,17652,36744,61440}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded436

theorem excluded437 : search 5 {240,4383,8738,17476,36744,61440}=false := by
  apply exclude 3 _ [{240,4383,8738,53196,61440},{4383,8738,17652,36744,61440}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded424,excluded436⟩

theorem excluded434 : search 6 {15,240,4369,8738,17476,36744,61440}=false := by
  apply exclude 4 _ [{15,240,4369,8738,36744,62532},{15,240,4369,8738,53196,61440},{15,240,4369,17476,36744,61986},{15,4369,8738,17652,36744,61440},{240,4383,8738,17476,36744,61440}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded416,excluded423,excluded431,excluded435,excluded437⟩

theorem excluded440 : search 4 {4383,8738,20292,35064,61440}=false := by
  apply exclude 2 _ [] (by decide) (by decide +kernel)
  simp

theorem excluded439 : search 5 {15,4369,8738,20292,35064,61440}=false := by
  apply exclude 3 _ [{4383,8738,20292,35064,61440}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded440

theorem excluded441 : search 5 {240,4383,8738,20292,34952,61440}=false := by
  apply exclude 3 _ [{240,4383,8738,53196,61440},{4383,8738,20292,35064,61440}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded424,excluded440⟩

theorem excluded438 : search 6 {15,240,4369,8738,20292,34952,61440}=false := by
  apply exclude 4 _ [{15,240,4369,8738,20292,63624},{15,240,4369,8738,53196,61440},{15,240,4369,20292,34952,61986},{15,4369,8738,20292,35064,61440},{240,4383,8738,20292,34952,61440}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded412,excluded423,excluded432,excluded439,excluded441⟩

theorem excluded443 : search 5 {240,4383,12066,17476,34952,61440}=false := by
  apply exclude 3 _ [{240,4383,12066,52428,61440}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded426

theorem excluded442 : search 6 {15,240,4369,12066,17476,34952,61440}=false := by
  apply exclude 4 _ [{15,240,4369,12066,17476,63624},{15,240,4369,12066,34952,62532},{15,240,4369,12066,52428,61440},{240,4383,12066,17476,34952,61440}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded413,excluded417,excluded425,excluded443⟩

theorem excluded445 : search 5 {3840,4383,8738,17476,35064,61440}=false := by
  apply exclude 3 _ [{3840,4383,8738,52476,61440},{4383,8738,20292,35064,61440}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded428,excluded440⟩

theorem excluded444 : search 6 {15,3840,4369,8738,17476,35064,61440}=false := by
  apply exclude 4 _ [{15,3840,4369,8738,35064,62532},{15,3840,4369,8738,52476,61440},{15,4369,8738,20292,35064,61440},{3840,4383,8738,17476,35064,61440}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded418,excluded427,excluded439,excluded445⟩

theorem excluded447 : search 5 {3840,4383,8738,17652,34952,61440}=false := by
  apply exclude 3 _ [{3840,4383,8738,52476,61440},{4383,8738,17652,36744,61440}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded428,excluded436⟩

theorem excluded446 : search 6 {15,3840,4369,8738,17652,34952,61440}=false := by
  apply exclude 4 _ [{15,3840,4369,8738,17652,63624},{15,3840,4369,8738,52476,61440},{15,4369,8738,17652,36744,61440},{3840,4383,8738,17652,34952,61440}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded414,excluded427,excluded435,excluded447⟩

theorem excluded448 : search 6 {240,3840,4383,8738,17476,34952,61440}=false := by
  apply exclude 4 _ [{240,3840,4383,8738,52428,61440},{240,4383,8738,17476,36744,61440},{240,4383,8738,20292,34952,61440},{240,4383,12066,17476,34952,61440},{3840,4383,8738,17476,35064,61440},{3840,4383,8738,17652,34952,61440}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded429,excluded437,excluded441,excluded443,excluded445,excluded447⟩

theorem excluded408 : search 7 {15,240,3840,4369,8738,17476,34952,61440}=false := by
  apply exclude 5 _ [{15,240,3840,4369,8738,17476,63624},{15,240,3840,4369,8738,34952,62532},{15,240,3840,4369,8738,52428,61440},{15,240,3840,4369,17476,34952,61986},{15,240,3840,8738,17476,34952,61713},{15,240,4369,8738,17476,36744,61440},{15,240,4369,8738,20292,34952,61440},{15,240,4369,12066,17476,34952,61440},{15,3840,4369,8738,17476,35064,61440},{15,3840,4369,8738,17652,34952,61440},{240,3840,4383,8738,17476,34952,61440}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded409,excluded415,excluded419,excluded430,excluded433,excluded434,excluded438,excluded442,excluded444,excluded446,excluded448⟩

theorem excluded452 : search 4 {0,240,4383,8738,53196}=false := by
  apply exclude 2 _ [] (by decide) (by decide +kernel)
  simp

theorem excluded451 : search 5 {0,15,240,4369,8738,53196}=false := by
  apply exclude 3 _ [{0,240,4383,8738,53196}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded452

theorem excluded454 : search 4 {0,240,4383,12066,52428}=false := by
  apply exclude 2 _ [] (by decide) (by decide +kernel)
  simp

theorem excluded453 : search 5 {0,15,240,4369,12066,52428}=false := by
  apply exclude 3 _ [{0,240,4383,12066,52428}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded454

theorem excluded456 : search 4 {0,3840,4383,8738,52476}=false := by
  apply exclude 2 _ [] (by decide) (by decide +kernel)
  simp

theorem excluded455 : search 5 {0,15,3840,4369,8738,52476}=false := by
  apply exclude 3 _ [{0,3840,4383,8738,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded456

theorem excluded457 : search 5 {0,240,3840,4383,8738,52428}=false := by
  apply exclude 3 _ [{0,240,4383,8738,53196},{0,240,4383,12066,52428},{0,3840,4383,8738,52476}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded452,excluded454,excluded456⟩

theorem excluded450 : search 6 {0,15,240,3840,4369,8738,52428}=false := by
  apply exclude 4 _ [{0,15,240,4369,8738,53196},{0,15,240,4369,12066,52428},{0,15,3840,4369,8738,52476},{0,240,3840,4383,8738,52428}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded451,excluded453,excluded455,excluded457⟩

theorem excluded460 : search 4 {0,4383,8738,17652,36744}=false := by
  apply exclude 2 _ [] (by decide) (by decide +kernel)
  simp

theorem excluded459 : search 5 {0,15,4369,8738,17652,36744}=false := by
  apply exclude 3 _ [{0,4383,8738,17652,36744}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded460

theorem excluded461 : search 5 {0,240,4383,8738,17476,36744}=false := by
  apply exclude 3 _ [{0,240,4383,8738,53196},{0,4383,8738,17652,36744}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded452,excluded460⟩

theorem excluded458 : search 6 {0,15,240,4369,8738,17476,36744}=false := by
  apply exclude 4 _ [{0,15,240,4369,8738,53196},{0,15,4369,8738,17652,36744},{0,240,4383,8738,17476,36744}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded451,excluded459,excluded461⟩

theorem excluded464 : search 4 {0,4383,8738,20292,35064}=false := by
  apply exclude 2 _ [] (by decide) (by decide +kernel)
  simp

theorem excluded463 : search 5 {0,15,4369,8738,20292,35064}=false := by
  apply exclude 3 _ [{0,4383,8738,20292,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded464

theorem excluded465 : search 5 {0,240,4383,8738,20292,34952}=false := by
  apply exclude 3 _ [{0,240,4383,8738,53196},{0,4383,8738,20292,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded452,excluded464⟩

theorem excluded462 : search 6 {0,15,240,4369,8738,20292,34952}=false := by
  apply exclude 4 _ [{0,15,240,4369,8738,53196},{0,15,4369,8738,20292,35064},{0,240,4383,8738,20292,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded451,excluded463,excluded465⟩

theorem excluded467 : search 5 {0,240,4383,12066,17476,34952}=false := by
  apply exclude 3 _ [{0,240,4383,12066,52428}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded454

theorem excluded466 : search 6 {0,15,240,4369,12066,17476,34952}=false := by
  apply exclude 4 _ [{0,15,240,4369,12066,52428},{0,240,4383,12066,17476,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded453,excluded467⟩

theorem excluded469 : search 5 {0,3840,4383,8738,17476,35064}=false := by
  apply exclude 3 _ [{0,3840,4383,8738,52476},{0,4383,8738,20292,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded456,excluded464⟩

theorem excluded468 : search 6 {0,15,3840,4369,8738,17476,35064}=false := by
  apply exclude 4 _ [{0,15,3840,4369,8738,52476},{0,15,4369,8738,20292,35064},{0,3840,4383,8738,17476,35064}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded455,excluded463,excluded469⟩

theorem excluded471 : search 5 {0,3840,4383,8738,17652,34952}=false := by
  apply exclude 3 _ [{0,3840,4383,8738,52476},{0,4383,8738,17652,36744}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded456,excluded460⟩

theorem excluded470 : search 6 {0,15,3840,4369,8738,17652,34952}=false := by
  apply exclude 4 _ [{0,15,3840,4369,8738,52476},{0,15,4369,8738,17652,36744},{0,3840,4383,8738,17652,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded455,excluded459,excluded471⟩

theorem excluded472 : search 6 {0,240,3840,4383,8738,17476,34952}=false := by
  apply exclude 4 _ [{0,240,3840,4383,8738,52428},{0,240,4383,8738,17476,36744},{0,240,4383,8738,20292,34952},{0,240,4383,12066,17476,34952},{0,3840,4383,8738,17476,35064},{0,3840,4383,8738,17652,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded457,excluded461,excluded465,excluded467,excluded469,excluded471⟩

theorem excluded449 : search 7 {0,15,240,3840,4369,8738,17476,34952}=false := by
  apply exclude 5 _ [{0,15,240,3840,4369,8738,52428},{0,15,240,4369,8738,17476,36744},{0,15,240,4369,8738,20292,34952},{0,15,240,4369,12066,17476,34952},{0,15,3840,4369,8738,17476,35064},{0,15,3840,4369,8738,17652,34952},{0,240,3840,4383,8738,17476,34952}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded450,excluded458,excluded462,excluded466,excluded468,excluded470,excluded472⟩

theorem excluded476 : search 4 {240,4383,8738,53196,65535}=false := by
  apply exclude 2 _ [] (by decide) (by decide +kernel)
  simp

theorem excluded475 : search 5 {15,240,4369,8738,53196,65535}=false := by
  apply exclude 3 _ [{240,4383,8738,53196,65535}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded476

theorem excluded478 : search 4 {240,4383,12066,52428,65535}=false := by
  apply exclude 2 _ [] (by decide) (by decide +kernel)
  simp

theorem excluded477 : search 5 {15,240,4369,12066,52428,65535}=false := by
  apply exclude 3 _ [{240,4383,12066,52428,65535}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded478

theorem excluded480 : search 4 {3840,4383,8738,52476,65535}=false := by
  apply exclude 2 _ [] (by decide) (by decide +kernel)
  simp

theorem excluded479 : search 5 {15,3840,4369,8738,52476,65535}=false := by
  apply exclude 3 _ [{3840,4383,8738,52476,65535}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded480

theorem excluded481 : search 5 {240,3840,4383,8738,52428,65535}=false := by
  apply exclude 3 _ [{240,4383,8738,53196,65535},{240,4383,12066,52428,65535},{3840,4383,8738,52476,65535}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded476,excluded478,excluded480⟩

theorem excluded474 : search 6 {15,240,3840,4369,8738,52428,65535}=false := by
  apply exclude 4 _ [{15,240,4369,8738,53196,65535},{15,240,4369,12066,52428,65535},{15,3840,4369,8738,52476,65535},{240,3840,4383,8738,52428,65535}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded475,excluded477,excluded479,excluded481⟩

theorem excluded484 : search 4 {4383,8738,17652,36744,65535}=false := by
  apply exclude 2 _ [] (by decide) (by decide +kernel)
  simp

theorem excluded483 : search 5 {15,4369,8738,17652,36744,65535}=false := by
  apply exclude 3 _ [{4383,8738,17652,36744,65535}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded484

theorem excluded485 : search 5 {240,4383,8738,17476,36744,65535}=false := by
  apply exclude 3 _ [{240,4383,8738,53196,65535},{4383,8738,17652,36744,65535}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded476,excluded484⟩

theorem excluded482 : search 6 {15,240,4369,8738,17476,36744,65535}=false := by
  apply exclude 4 _ [{15,240,4369,8738,53196,65535},{15,4369,8738,17652,36744,65535},{240,4383,8738,17476,36744,65535}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded475,excluded483,excluded485⟩

theorem excluded488 : search 4 {4383,8738,20292,35064,65535}=false := by
  apply exclude 2 _ [] (by decide) (by decide +kernel)
  simp

theorem excluded487 : search 5 {15,4369,8738,20292,35064,65535}=false := by
  apply exclude 3 _ [{4383,8738,20292,35064,65535}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded488

theorem excluded489 : search 5 {240,4383,8738,20292,34952,65535}=false := by
  apply exclude 3 _ [{240,4383,8738,53196,65535},{4383,8738,20292,35064,65535}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded476,excluded488⟩

theorem excluded486 : search 6 {15,240,4369,8738,20292,34952,65535}=false := by
  apply exclude 4 _ [{15,240,4369,8738,53196,65535},{15,4369,8738,20292,35064,65535},{240,4383,8738,20292,34952,65535}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded475,excluded487,excluded489⟩

theorem excluded491 : search 5 {240,4383,12066,17476,34952,65535}=false := by
  apply exclude 3 _ [{240,4383,12066,52428,65535}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact excluded478

theorem excluded490 : search 6 {15,240,4369,12066,17476,34952,65535}=false := by
  apply exclude 4 _ [{15,240,4369,12066,52428,65535},{240,4383,12066,17476,34952,65535}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded477,excluded491⟩

theorem excluded493 : search 5 {3840,4383,8738,17476,35064,65535}=false := by
  apply exclude 3 _ [{3840,4383,8738,52476,65535},{4383,8738,20292,35064,65535}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded480,excluded488⟩

theorem excluded492 : search 6 {15,3840,4369,8738,17476,35064,65535}=false := by
  apply exclude 4 _ [{15,3840,4369,8738,52476,65535},{15,4369,8738,20292,35064,65535},{3840,4383,8738,17476,35064,65535}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded479,excluded487,excluded493⟩

theorem excluded495 : search 5 {3840,4383,8738,17652,34952,65535}=false := by
  apply exclude 3 _ [{3840,4383,8738,52476,65535},{4383,8738,17652,36744,65535}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded480,excluded484⟩

theorem excluded494 : search 6 {15,3840,4369,8738,17652,34952,65535}=false := by
  apply exclude 4 _ [{15,3840,4369,8738,52476,65535},{15,4369,8738,17652,36744,65535},{3840,4383,8738,17652,34952,65535}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded479,excluded483,excluded495⟩

theorem excluded496 : search 6 {240,3840,4383,8738,17476,34952,65535}=false := by
  apply exclude 4 _ [{240,3840,4383,8738,52428,65535},{240,4383,8738,17476,36744,65535},{240,4383,8738,20292,34952,65535},{240,4383,12066,17476,34952,65535},{3840,4383,8738,17476,35064,65535},{3840,4383,8738,17652,34952,65535}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded481,excluded485,excluded489,excluded491,excluded493,excluded495⟩

theorem excluded473 : search 7 {15,240,3840,4369,8738,17476,34952,65535}=false := by
  apply exclude 5 _ [{15,240,3840,4369,8738,52428,65535},{15,240,4369,8738,17476,36744,65535},{15,240,4369,8738,20292,34952,65535},{15,240,4369,12066,17476,34952,65535},{15,3840,4369,8738,17476,35064,65535},{15,3840,4369,8738,17652,34952,65535},{240,3840,4383,8738,17476,34952,65535}] (by decide) (by decide +kernel)
  simp only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded474,excluded482,excluded486,excluded490,excluded492,excluded494,excluded496⟩

def roots : List (Nat × Pool) := [(6,{15,240,3840,4369,8738,17476,34952}),(7,{15,240,3840,4369,8738,17476,34952}),(7,{15,240,3840,4369,8738,17476,34952,61440}),(7,{0,15,240,3840,4369,8738,17476,34952}),(7,{15,240,3840,4369,8738,17476,34952,65535})]
theorem no_root : ∀ z∈roots, search z.1 z.2=false := by
  simp only [roots,List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true]
  exact ⟨excluded0,excluded24,excluded408,excluded449,excluded473⟩

def required : Pool := {15,240,3840,4369,8738,17476,34952}

lemma required_subset {S : Pool} (sub : S⊆raw) (sep : Separates S) : required ⊆ S := by
  have witnesses : ∀ w∈required, ∃ p∈pos, ∃ n∈neg, ∀ v∈raw,
      v.testBit p=true → v.testBit n=false → v=w := by decide
  intro w hw
  obtain ⟨p,hp,n,hn,only⟩ := witnesses w hw
  obtain ⟨v,hv,yes,no⟩ := sep p hp n hn
  exact (only v (sub hv) yes no) ▸ hv

-- The first pool must contain seven particular input masks.
lemma no_small : ¬Possible raw 7 := by
  rintro ⟨k,hk,S,sub,adm,sep,hit⟩
  have req := required_subset sub sep
  let Z := S \ required
  have rest : Z ∈ (raw \ required).powerset := Finset.mem_powerset.mpr (Finset.sdiff_subset_sdiff_left required sub)
  have eq : required ∪ Z = S := Finset.union_sdiff_of_subset req
  have lookup : ∀ j : Fin 8, ∀ E∈(raw \ required).powerset,
      (required ∪ E).card ≤ j.val+1 → (j.val,required ∪ E)∈roots := by decide +kernel
  have recorded := lookup ⟨k,by omega⟩ Z rest (by simpa only [eq] using adm)
  exact Bool.noConfusion (hit.symm.trans (no_root (k,S) (by simpa only [eq] using recorded)))

end PEqualNP.Outside.L_meta_5940_aux

theorem PEqualNP.Outside.L_meta_5940 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (318 : ℕ).testBit (4 * u.val + v.val)) 8 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (318 : ℕ).testBit (4 * u.val + v.val)) 7 := by
  refine ⟨PEqualNP.Outside.L_meta_5940_aux.upper,?_⟩
  rintro ⟨C,mono,size,rep⟩
  exact PEqualNP.Outside.L_meta_5940_aux.no_small (PEqualNP.Outside.L_meta_5940_aux.necessary C mono size rep)
