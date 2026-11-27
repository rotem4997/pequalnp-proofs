import Mathlib.Tactic
import PEqualNP.Defs

-- A binary formula records the dependencies of the circuit output.
namespace PEqualNP.Outside.L_meta_5527_aux

abbrev Tree := FreeAlgebra.Pre Bool Nat

def Tree.node (k : Bool) (a b : Tree) : Tree := if k then .mul a b else .add a b

def Tree.leaves : Tree → List Nat
  | .of i => [i]
  | .ofScalar _ => []
  | .add a b => (Tree.leaves a) ++ (Tree.leaves b)
  | .mul a b => (Tree.leaves a) ++ (Tree.leaves b)

def Tree.eval : Tree → List Bool → Bool
  | .of i, x => x.getD i false
  | .ofScalar b, _ => b
  | .add a b, x => (Tree.eval a x) || (Tree.eval b x)
  | .mul a b, x => (Tree.eval a x) && (Tree.eval b x)

end PEqualNP.Outside.L_meta_5527_aux

-- Replacing a wire by a gate can increase the number of distinct leaves, with a one-unit penalty for repetition, by at most one.
namespace PEqualNP.Outside.L_meta_5527_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def Tree.replace (t : Tree) (i : Nat) (r : Tree) : Tree :=
  match t with
  | .of j => if j = i then r else .of j
  | .ofScalar b => .ofScalar b
  | .add a b => .add (Tree.replace a i r) (Tree.replace b i r)
  | .mul a b => .mul (Tree.replace a i r) (Tree.replace b i r)

def splice (i : Nat) (r : List Nat) (l : List Nat) : List Nat :=
  l.flatMap fun j => if j = i then r else [j]

lemma Tree.replace_leaves (t r : Tree) (i : Nat) :
    (t.replace i r).leaves = splice i r.leaves t.leaves := by
  induction t with
  | of j => by_cases e : j=i <;> simp [Tree.replace,Tree.leaves,splice,e]
  | ofScalar b => simp [Tree.replace,Tree.leaves,splice]
  | add a b ha hb => simp [Tree.replace,Tree.leaves,splice,ha,hb,List.flatMap_append]
  | mul a b ha hb => simp [Tree.replace,Tree.leaves,splice,ha,hb,List.flatMap_append]

def credit (l : List Nat) : Nat := l.toFinset.card + if l.Nodup then 0 else 1

lemma credit_length (l : List Nat) : credit l ≤ l.length := by
  have h := l.toFinset_card_le
  by_cases d : l.Nodup
  · simpa [credit,d] using h
  · have diff : l.toFinset.card ≠ l.length := fun e => d
      (List.nodup_iff_length_dedup_eq.mpr (by simpa [List.card_toFinset] using e))
    simp [credit,d]; omega

lemma splice_absent (i : Nat) (r l : List Nat) (absent : i ∉ l) : splice i r l = l := by
  induction l with
  | nil => rfl
  | cons a l h =>
    simp only [List.mem_cons,not_or] at absent
    obtain ⟨ne,no⟩ := absent
    simpa [splice,Ne.symm ne] using h no

lemma splice_length (i : Nat) (r l : List Nat) (d : l.Nodup) (hr : r.length ≤ 2) :
    (splice i r l).length ≤ l.length + 1 := by
  induction l with
  | nil => simp [splice]
  | cons a l h =>
    obtain ⟨ne,no⟩ := List.nodup_cons.mp d
    by_cases e : a=i
    · subst a
      change ((if i=i then r else [i]) ++ splice i r l).length ≤ _ 
      simp [splice_absent _ _ _ ne]; omega
    · change ((if a=i then r else [a]) ++ splice i r l).length ≤ _
      simp [e]; have := h no; omega

lemma splice_card (i : Nat) (r l : List Nat) (hr : r.length ≤ 2) :
    (splice i r l).toFinset.card ≤ l.toFinset.card + 1 := by
  by_cases hi : i ∈ l
  · have sub : (splice i r l).toFinset ⊆ l.toFinset.erase i ∪ r.toFinset := by
      intro v hv
      obtain ⟨j,hj,hv⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hv)
      by_cases e : j = i
      · exact Finset.mem_union_right _ (List.mem_toFinset.mpr (by simpa [e] using hv))
      · have h : v=j := by simpa [e] using hv
        subst v; exact Finset.mem_union_left _
          (Finset.mem_erase.mpr ⟨e,List.mem_toFinset.mpr hj⟩)
    have c := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
    have he := Finset.card_erase_add_one (List.mem_toFinset.mpr hi)
    have cr := r.toFinset_card_le
    omega
  · simp [splice_absent _ _ _ hi]

lemma credit_splice (i : Nat) (r l : List Nat) (hr : r.length ≤ 2) :
    credit (splice i r l) ≤ credit l + 1 := by
  by_cases d : l.Nodup
  · have a := (credit_length (splice i r l)).trans (splice_length i r l d hr)
    simpa [credit,d,List.toFinset_card_of_nodup d] using a
  · have a := splice_card i r l hr
    simp only [credit,ite_eq_right d]
    split <;> omega

def gateTree (g : Gate) : Tree :=
  match g.inputs with
  | [] => .ofScalar (match g.op with | .and => true | _ => false)
  | [a] => .of a
  | a::b::_ => Tree.node (match g.op with | .and => true | _ => false) (.of a) (.of b)

lemma gate_leaves (g : Gate) : (gateTree g).leaves.length ≤ 2 := by
  unfold gateTree
  split
  · exact Nat.zero_le _
  · exact Nat.le_succ 1
  · unfold Tree.node
    split <;> exact Nat.le_refl 2

def back (n : Nat) : List Gate → Tree → Tree
  | [], t => t
  | g::gs, t => (back (n+1) gs t).replace n (gateTree g)

lemma back_credit (n : Nat) (gs : List Gate) (t : Tree) :
    credit (back n gs t).leaves ≤ credit t.leaves + gs.length := by
  induction gs generalizing n with
  | nil => simp [back]
  | cons g gs ih =>
    simp only [back,Tree.replace_leaves,List.length_cons]
    have h := credit_splice n (gateTree g).leaves (back (n+1) gs t).leaves (gate_leaves g)
    have h' := ih (n+1)
    omega

def push (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma eval_gate (g : Gate) (h : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (w : List Bool) : (gateTree g).eval w = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  rcases g with ⟨op,ins⟩
  obtain ⟨hop,hlen⟩ := h
  change op = .and ∨ op = .or at hop
  change ins.length ≤ 2 at hlen
  cases ins with
  | nil => rcases hop with rfl | rfl <;> rfl
  | cons a ins =>
    cases ins with
    | nil => rcases hop with rfl | rfl <;> simp [gateTree,Tree.eval,GateOp.eval]
    | cons b ins =>
      cases ins with
      | nil => rcases hop with rfl | rfl <;> simp [gateTree,Tree.node,Tree.eval,GateOp.eval]
      | cons c ins => simp at hlen

lemma Tree.replace_eval (t r : Tree) (w : List Bool) :
    (t.replace w.length r).eval w = t.eval (w ++ [r.eval w]) := by
  induction t with
  | of i =>
    by_cases e : i=w.length
    · simp [Tree.replace,Tree.eval,e]
    by_cases lt : i<w.length
    · simp only [Tree.replace,ite_eq_right e,Tree.eval]
      rw [List.getD_append _ _ _ _ lt]
    · have ow : w.length ≤ i := by omega
      have ow' : (w ++ [r.eval w]).length ≤ i := by simp; omega
      simp only [Tree.replace,ite_eq_right e,Tree.eval]
      rw [List.getD_eq_default _ _ ow,List.getD_eq_default _ _ ow']
  | ofScalar b => rfl
  | add a b ha hb => simp [Tree.replace,Tree.eval,ha,hb]
  | mul a b ha hb => simp [Tree.replace,Tree.eval,ha,hb]

lemma back_eval (gs : List Gate) (t : Tree) (w : List Bool)
    (h : ∀ g∈gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (back w.length gs t).eval w = t.eval (gs.foldl push w) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [back,Tree.replace_eval,List.foldl_cons]
    rw [eval_gate g (h g (by simp)) w]
    change (back (w.length+1) gs t).eval (push w g) = _
    have leng : (push w g).length = w.length+1 := by simp [push]
    rw [←leng]
    exact ih (push w g) (fun g hg => h g (by simp [hg]))

theorem formula_bridge (C : Circuit) (n : Nat) (hc : Monotone2 C) :
    ∃ t : Tree, (∀ x : List Bool, x.length = n → t.eval x = C.eval x) ∧
      t.leaves.toFinset.card + (if t.leaves.Nodup then 0 else 1) ≤ C.size+1 := by
  refine ⟨back n C.gates (.of C.output), ?_, ?_⟩
  · intro x hx
    rw [←hx,back_eval _ _ _ hc]
    rfl
  · simpa [credit,Tree.leaves,Circuit.size,Nat.add_comm] using
      back_credit n C.gates (.of C.output)

end PEqualNP.Outside.L_meta_5527_aux

-- The nine restricted inputs are the empty input, four singletons and four pairs. Each table lists the attainable signatures for its set of variables.
namespace PEqualNP.Outside.L_meta_5527_aux

def projectedWire (i : Fin 4) : Nat := ![1,2,4,5] i

def selected (ws : List Nat) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => projectedWire i ∈ ws)

def supportCode (s : Finset (Fin 4)) : Nat :=
  (if 0 ∈ s then 1 else 0) + (if 1 ∈ s then 2 else 0) +
  (if 2 ∈ s then 4 else 0) + (if 3 ∈ s then 8 else 0)

def allowed (s : Finset (Fin 4)) : List (BitVec 9) :=
  match supportCode s with
  | 0 => [0, 511]
  | 1 => [0, 98, 511]
  | 2 => [0, 388, 511]
  | 3 => [0, 98, 388, 486, 511]
  | 4 => [0, 168, 511]
  | 5 => [0, 32, 98, 168, 234, 511]
  | 6 => [0, 128, 168, 388, 428, 511]
  | 7 => [0, 32, 98, 128, 160, 168, 226, 234, 388, 420, 428, 486, 494, 511]
  | 8 => [0, 336, 511]
  | 9 => [0, 64, 98, 336, 370, 511]
  | 10 => [0, 256, 336, 388, 468, 511]
  | 11 => [0, 64, 98, 256, 320, 336, 354, 370, 388, 452, 468, 486, 502, 511]
  | 12 => [0, 168, 336, 504, 511]
  | 13 => [0, 32, 64, 96, 98, 168, 232, 234, 336, 368, 370, 504, 506, 511]
  | 14 => [0, 128, 168, 256, 336, 384, 388, 424, 428, 464, 468, 504, 508, 511]
  | 15 => [0, 32, 64, 96, 98, 128, 160, 168, 192, 226, 232, 234, 256, 288, 320, 336, 354, 368, 370, 384, 388, 420, 424, 428, 452, 464, 468, 480, 482, 484, 486, 488, 490, 492, 494, 496, 498, 500, 502, 504, 506, 508, 510, 511]
  | _ => []

theorem selected_append (x y : List Nat) : selected (x ++ y) = selected x ∪ selected y := by
  ext i
  simp [selected]

theorem selected_disjoint {x y : List Nat} (h : List.Disjoint x y) :
    Disjoint (selected x) (selected y) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  simp only [selected, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  exact h hi hj

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem allowed_closed : ∀ s t : Finset (Fin 4), Disjoint s t →
    (allowed s).all (fun a => (allowed t).all (fun b =>
      decide (a &&& b ∈ allowed (s ∪ t)) && decide (a ||| b ∈ allowed (s ∪ t)))) = true := by
  decide

theorem allowed_merge {s t : Finset (Fin 4)} (hd : Disjoint s t)
    {a b : BitVec 9} (ha : a ∈ allowed s) (hb : b ∈ allowed t) :
    a &&& b ∈ allowed (s ∪ t) ∧ a ||| b ∈ allowed (s ∪ t) := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp (allowed_closed s t hd) a ha) b hb
  simpa using h

theorem target_missing : ∀ s : Finset (Fin 4), (224 : BitVec 9) ∉ allowed s := by decide


def rawSignature (i : Nat) : BitVec 9 :=
  if i = 1 then 98 else if i = 2 then 388 else if i = 4 then 168 else if i = 5 then 336 else 0

def sample (r : Fin 9) : List Bool :=
  List.ofFn fun i : Fin 8 => (rawSignature i.val).getLsbD r.val

def Tree.signature : Tree → BitVec 9
  | .of i => rawSignature i
  | .ofScalar b => if b then 511 else 0
  | .add a b => Tree.signature a ||| Tree.signature b
  | .mul a b => Tree.signature a &&& Tree.signature b

theorem sample_length (r : Fin 9) : (sample r).length = 8 := by simp [sample]

theorem rawSignature_of_large {i : Nat} (hi : 8 ≤ i) : rawSignature i = 0 := by
  simp [rawSignature, show i ≠ 1 by omega, show i ≠ 2 by omega,
    show i ≠ 4 by omega, show i ≠ 5 by omega]

theorem selected_large {i : Nat} (hi : 8 ≤ i) : selected [i] = ∅ := by
  ext v
  simp only [selected, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_singleton,
    Finset.notMem_empty, iff_false]
  fin_cases v <;> simp [projectedWire] <;> omega

theorem raw_allowed (i : Nat) : rawSignature i ∈ allowed (selected [i]) := by
  by_cases h : i < 8
  · exact (of_decide_eq_true (show decide (∀ j : Fin 8,
      rawSignature j.val ∈ allowed (selected [j.val])) = true from rfl)) ⟨i,h⟩
  · have hi : 8 ≤ i := by omega
    rw [rawSignature_of_large hi, selected_large hi]
    decide

theorem signature_allowed (t : Tree) (ht : t.leaves.Nodup) :
    t.signature ∈ allowed (selected t.leaves) := by
  induction t with
  | of i => exact raw_allowed i
  | ofScalar b => cases b <;> decide
  | add a b ia ib =>
    obtain ⟨ha,hb,hab⟩ := List.nodup_append.mp ht
    have hd : List.Disjoint (Tree.leaves a) (Tree.leaves b) := by
      intro n hn hm
      exact hab n hn n hm rfl
    have H := allowed_merge (selected_disjoint hd) (ia ha) (ib hb)
    change _ ∈ allowed (selected ((Tree.leaves a) ++ (Tree.leaves b)))
    rw [selected_append]
    exact H.2
  | mul a b ia ib =>
    obtain ⟨ha,hb,hab⟩ := List.nodup_append.mp ht
    have hd : List.Disjoint (Tree.leaves a) (Tree.leaves b) := by
      intro n hn hm
      exact hab n hn n hm rfl
    have H := allowed_merge (selected_disjoint hd) (ia ha) (ib hb)
    change _ ∈ allowed (selected ((Tree.leaves a) ++ (Tree.leaves b)))
    rw [selected_append]
    exact H.1

theorem signature_sem (t : Tree) (r : Fin 9) :
    t.signature.getLsbD r.val = t.eval (sample r) := by
  induction t with
  | of i =>
    by_cases hi : i < 8
    · interval_cases i <;> rfl
    · have hh : 8 ≤ i := by omega
      simp [Tree.signature, Tree.eval, rawSignature_of_large hh, sample, List.getD,
        hi]
  | ofScalar b =>
    have hh : ∀ (b : Bool) (r : Fin 9),
        ((if b then 511 else 0 : BitVec 9).getLsbD r.val) = b := by decide
    exact hh b r
  | add a b ia ib =>
    simp only [Tree.signature, Tree.eval, BitVec.getLsbD_or, ia, ib]
  | mul a b ia ib =>
    simp only [Tree.signature, Tree.eval, BitVec.getLsbD_and, ia, ib]

theorem no_readonce (t : Tree) (ht : t.leaves.Nodup)
    (he : ∀ r : Fin 9, t.eval (sample r) = (224 : BitVec 9).getLsbD r.val) : False := by
  have eq : t.signature = 224 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    exact (signature_sem t ⟨i,hi⟩).trans (he ⟨i,hi⟩)
  have hm := signature_allowed t ht
  rw [eq] at hm
  exact target_missing _ hm

end PEqualNP.Outside.L_meta_5527_aux

-- Seven input variables are essential for the promised rows of this graph.
namespace PEqualNP.Outside.L_meta_5527_aux.Support
open PEqualNP.Represents PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def adj (u v : Fin 4) : Bool := (316 : ℕ).testBit (4*u.val+v.val)

def rowInput (u v : Fin 4) : Fin 8→Bool :=
  Fin.addCases (motive:=fun _ : Fin (4+4)=>Bool)
    (fun i : Fin 4=>decide (i=u)) (fun j : Fin 4=>decide (j=v))

theorem rowInput_eq (u v : Fin 4) : List.ofFn (rowInput u v)=oneEach u v := by
  revert u v
  decide +kernel

def BitRep (f : (Fin 8→Bool)→Bool) : Prop :=
  ∀ u v : Fin 4, f (rowInput u v)=adj u v

def mandatory : Finset (Fin 8) := {0,1,2,4,5,6,7}
def must (i : Fin 7) : Fin 8 := (![0,1,2,4,5,6,7] : Fin 7→Fin 8) i

def yesU : Fin 7→Fin 4 := ![0,1,2,2,1,0,0]
def yesV : Fin 7→Fin 4 := ![2,1,0,0,1,2,3]
def noU : Fin 7→Fin 4 := ![3,3,3,2,1,0,0]
def noV : Fin 7→Fin 4 := ![2,1,0,1,2,0,0]

theorem witness : ∀ i : Fin 7, adj (yesU i) (yesV i)=true ∧ adj (noU i) (noV i)=false ∧
    ∀ k : Fin 8, k≠must i → rowInput (yesU i) (yesV i) k=true →
      rowInput (noU i) (noV i) k=true := by decide +kernel

theorem must_complete : ∀ i : Fin 8, i∈mandatory → ∃ j : Fin 7, must j=i := by decide +kernel

theorem essential (f : (Fin 8→Bool)→Bool) (mono : Monotone f) (rep : BitRep f)
    (i : Fin 8) (hi : i∈mandatory) :
    ∃ x y : Fin 8→Bool, (∀ k, k≠i → x k=y k) ∧ f x≠f y := by
  obtain ⟨j,rfl⟩ := must_complete i hi
  obtain ⟨hyes,hno,rel⟩ := witness j
  let x := rowInput (yesU j) (yesV j)
  let y (k : Fin 8) := if k=must j then false else x k
  have fx : f x=true := (rep _ _).trans hyes
  have fn : f (rowInput (noU j) (noV j))=false := (rep _ _).trans hno
  have le : y≤rowInput (noU j) (noV j) := by
    intro k
    apply Bool.le_iff_imp.mpr
    intro hk
    by_cases e : k=must j
    · simp [y,e] at hk
    · exact rel k e (by simpa [y,e] using hk)
  have fy : f y=false := by
    have h := mono le
    rw [fn] at h
    exact Bool.eq_false_of_le_false h
  exact ⟨x,y,fun k hk=>by simp [y,hk],by rw [fx,fy]; decide⟩

theorem necessary_in_support (f : (Fin 8→Bool)→Bool) (mono : Monotone f) (rep : BitRep f)
    (S : Finset ℕ) (dep : ∀ x y : Fin 8→Bool, (∀ k : Fin 8, k.val∈S→x k=y k) → f x=f y)
    (i : Fin 8) (hi : i∈mandatory) : i.val∈S := by
  by_contra notin
  obtain ⟨x,y,eq,ne⟩ := essential f mono rep i hi
  apply ne
  apply dep
  intro k hk
  exact eq k (fun e=>notin (e ▸ hk))

theorem support_lower (f : (Fin 8→Bool)→Bool) (mono : Monotone f) (rep : BitRep f)
    (S : Finset ℕ) (dep : ∀ x y : Fin 8→Bool, (∀ k : Fin 8, k.val∈S→x k=y k) → f x=f y) :
    7≤S.card := by
  have sub : mandatory.image Fin.val ⊆ S := by
    intro k hk
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hk
    exact necessary_in_support f mono rep S dep i hi
  have h := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ Fin.val_injective] at h
  exact h

def negU : Fin 8→Fin 4 := ![0,1,2,3,3,3,3,3]
def negV : Fin 8→Fin 4 := ![0,2,1,0,0,1,2,3]

theorem negWitness : ∀ i : Fin 8, adj (negU i) (negV i)=false ∧
  rowInput (negU i) (negV i) i=true := by decide +kernel

def singleton (i : Fin 8) (k : Fin 8) : Bool := decide (k=i)

theorem singleton_false (f : (Fin 8→Bool)→Bool) (mono : Monotone f) (rep : BitRep f)
    (i : Fin 8) : f (singleton i)=false := by
  obtain ⟨hno,hi⟩ := negWitness i
  have le : singleton i≤rowInput (negU i) (negV i) := by
    intro k
    apply Bool.le_iff_imp.mpr
    intro hk
    have e : k=i := of_decide_eq_true hk
    exact e.symm ▸ hi
  have h := mono le
  rw [(rep _ _).trans hno] at h
  exact Bool.eq_false_of_le_false h

theorem empty_false (f : (Fin 8→Bool)→Bool) (mono : Monotone f) (rep : BitRep f) :
    f (fun _=>false)=false := by
  have le : (fun _ : Fin 8=>false)≤singleton 0 := fun k=>Bool.false_le _
  have h := mono le
  rw [singleton_false f mono rep 0] at h
  exact Bool.eq_false_of_le_false h

def reduced (r : Fin 9) : Fin 8→Bool :=
  let masks : Fin 9→ℕ := ![0,2,4,16,32,18,34,20,36]
  fun k=>(masks r).testBit k.val

theorem reduced_shape : reduced 0=(fun _=>false) ∧
    reduced 1=singleton 1 ∧ reduced 2=singleton 2 ∧
    reduced 3=singleton 4 ∧ reduced 4=singleton 5 ∧
    reduced 5=rowInput 1 0 ∧ reduced 6=rowInput 1 1 ∧
    reduced 7=rowInput 2 0 ∧ reduced 8=rowInput 2 1 := by
  repeat' apply And.intro
  all_goals funext k; revert k; decide +kernel

theorem reduced_eval (f : (Fin 8→Bool)→Bool) (mono : Monotone f) (rep : BitRep f) :
    ∀ r : Fin 9, f (reduced r)=(224 : ℕ).testBit r.val := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩ := reduced_shape
  intro r
  fin_cases r
  · change f (reduced 0)=false
    rw [h0,empty_false f mono rep]
  · change f (reduced 1)=false
    rw [h1,singleton_false f mono rep]
  · change f (reduced 2)=false
    rw [h2,singleton_false f mono rep]
  · change f (reduced 3)=false
    rw [h3,singleton_false f mono rep]
  · change f (reduced 4)=false
    rw [h4,singleton_false f mono rep]
  · change f (reduced 5)=true
    rw [h5,rep]
    rfl
  · change f (reduced 6)=true
    rw [h6,rep]
    rfl
  · change f (reduced 7)=true
    rw [h7,rep]
    rfl
  · change f (reduced 8)=false
    rw [h8,rep]
    rfl

theorem circuit_rep (C : Circuit) (rep : Represents adj C) :
    BitRep (fun x=>C.eval (List.ofFn x)) := by
  intro u v
  change C.eval (List.ofFn (rowInput u v)) = adj u v
  rw [rowInput_eq]
  exact rep u v

end PEqualNP.Outside.L_meta_5527_aux.Support

-- Transfer the support bound and the values on the restricted inputs to the formula.
namespace PEqualNP.Outside.L_meta_5527_aux.Support
open PEqualNP.Represents PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem tree_agree (t : Tree) (x y : List Bool)
    (agree : ∀ i∈t.leaves, x.getD i false=y.getD i false) :
    t.eval x=t.eval y := by
  induction t with
  | of i => exact agree i (by simp [Tree.leaves])
  | ofScalar b => rfl
  | add a b ha hb =>
    have left := ha (fun i hi=>agree i (by simp [Tree.leaves,hi]))
    have right := hb (fun i hi=>agree i (by simp [Tree.leaves,hi]))
    simp only [Tree.eval,left,right]
  | mul a b ha hb =>
    have left := ha (fun i hi=>agree i (by simp [Tree.leaves,hi]))
    have right := hb (fun i hi=>agree i (by simp [Tree.leaves,hi]))
    simp only [Tree.eval,left,right]

theorem bool_op_mono : ∀ a b c d k : Bool, a≤c → b≤d →
    (if k then a&&b else a||b) ≤ (if k then c&&d else c||d) := by decide +kernel

theorem list_tree_mono (t : Tree) (x y : List Bool)
    (le : ∀ i, x.getD i false≤y.getD i false) :
    t.eval x≤t.eval y := by
  induction t with
  | of i => exact le i
  | ofScalar b => exact le_rfl
  | add a b ha hb => exact bool_op_mono _ _ _ _ false ha hb
  | mul a b ha hb => exact bool_op_mono _ _ _ _ true ha hb

theorem tree_mono (t : Tree) : Monotone (fun x : Fin 8→Bool=>t.eval (List.ofFn x)) := by
  intro x y le
  apply list_tree_mono
  intro i
  by_cases hi : i<8
  · rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getD_eq_getElem _ _ (by simpa using hi)]
    simpa only [List.getElem_ofFn] using le ⟨i,hi⟩
  · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp;omega)]

theorem tree_dep (t : Tree) (x y : Fin 8→Bool)
    (eq : ∀ k : Fin 8, k.val∈t.leaves.toFinset → x k=y k) :
    t.eval (List.ofFn x)=t.eval (List.ofFn y) := by
  apply tree_agree
  intro i hi
  by_cases hraw : i<8
  · rw [List.getD_eq_getElem _ _ (by simpa using hraw),List.getD_eq_getElem _ _ (by simpa using hraw)]
    simpa only [List.getElem_ofFn] using eq ⟨i,hraw⟩ (List.mem_toFinset.mpr hi)
  · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp;omega)]

theorem tree_rep (t : Tree) (C : Circuit) (rep : Represents adj C)
    (agree : ∀ x : List Bool, x.length=8 → t.eval x=C.eval x) :
    BitRep (fun x=>t.eval (List.ofFn x)) := by
  intro u v
  change t.eval (List.ofFn (rowInput u v))=adj u v
  rw [agree _ (by simp),rowInput_eq]
  exact rep u v

theorem tree_support_lower (t : Tree) (C : Circuit) (rep : Represents adj C)
    (agree : ∀ x : List Bool, x.length=8 → t.eval x=C.eval x) :
    7≤t.leaves.toFinset.card :=
  support_lower _ (tree_mono t) (tree_rep t C rep agree) _ (tree_dep t)

theorem tree_necessary (t : Tree) (C : Circuit) (rep : Represents adj C)
    (agree : ∀ x : List Bool, x.length=8 → t.eval x=C.eval x)
    (i : Fin 8) (hi : i∈mandatory) : i.val∈t.leaves :=
  List.mem_toFinset.mp (necessary_in_support _ (tree_mono t) (tree_rep t C rep agree) _ (tree_dep t) i hi)

theorem tree_reduced_eval (t : Tree) (C : Circuit) (rep : Represents adj C)
    (agree : ∀ x : List Bool, x.length=8 → t.eval x=C.eval x) :
    ∀ r : Fin 9, t.eval (List.ofFn (reduced r))=(224 : ℕ).testBit r.val :=
  reduced_eval _ (tree_mono t) (tree_rep t C rep agree)

end PEqualNP.Outside.L_meta_5527_aux.Support

-- Identify the nine restrictions with the signatures used by the finite table.
namespace PEqualNP.Outside.L_meta_5527_aux.Support
open PEqualNP.Represents PEqualNP.CircuitLowerBounds

theorem sample_eq : ∀ r : Fin 9, List.ofFn (reduced r)=sample r := by decide +kernel

theorem mask_eq : ∀ r : Fin 9, (224:ℕ).testBit r.val=(224:BitVec 9).getLsbD r.val := by decide +kernel

theorem tree_sample_eval (t : Tree) (C : Circuit) (rep : Represents adj C)
    (agree : ∀ x : List Bool, x.length=8 → t.eval x=C.eval x) :
    ∀ r : Fin 9, t.eval (sample r)=(224 : BitVec 9).getLsbD r.val := by
  intro r
  rw [← sample_eq r,← mask_eq r]
  exact tree_reduced_eval t C rep agree r

end PEqualNP.Outside.L_meta_5527_aux.Support

-- An explicit seven-gate circuit represents the three nonempty rows.
namespace PEqualNP.Outside.L_meta_5527_aux.Upper
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C : Circuit :=
  ⟨[⟨.or,[6,7]⟩, ⟨.and,[0,8]⟩,
    ⟨.or,[4,5]⟩, ⟨.and,[1,10]⟩,
    ⟨.and,[2,4]⟩, ⟨.or,[9,11]⟩, ⟨.or,[13,12]⟩], 14⟩

theorem upper : RepSizeAtMost (fun u v : Fin 4 => (316 : ℕ).testBit (4*u.val+v.val)) 7 := by
  refine ⟨C,?_,by decide +kernel,by decide +kernel⟩
  intro g hg
  simp only [C,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp

end PEqualNP.Outside.L_meta_5527_aux.Upper

open PEqualNP.Outside.L_meta_5527_aux

theorem PEqualNP.Outside.L_meta_5527 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (316 : ℕ).testBit (4 * u.val + v.val)) 7 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (316 : ℕ).testBit (4 * u.val + v.val)) 6 := by
  refine ⟨Upper.upper, ?_⟩
  rintro ⟨C, hC, hsize, hrep⟩
  obtain ⟨t, heval, hcount⟩ := formula_bridge C 8 hC
  have hseven := Support.tree_support_lower t C hrep heval
  have ht : t.leaves.Nodup := by
    by_contra hn
    simp only [ite_eq_right hn] at hcount
    omega
  exact no_readonce t ht (Support.tree_sample_eval t C hrep heval)
