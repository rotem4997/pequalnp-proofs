import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18350
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

abbrev Ref := Bool ⊕ Nat

def evalRef (w : List Bool) : Ref → Bool
  | .inl b => b
  | .inr j => w.getD j false

def isFalseRef : Ref → Bool
  | .inl b => !b
  | .inr _ => false

def isTrueRef : Ref → Bool
  | .inl b => b
  | .inr _ => false

def liveRef : Ref → Option Nat
  | .inl _ => none
  | .inr i => some i

def shrink (op : GateOp) (xs : List Ref) : Gate :=
  match op with
  | .not => match xs.headD (.inl false) with
    | .inl b => ⟨if b then .or else .and, []⟩
    | .inr i => ⟨.not,[i]⟩
  | .or => if xs.any isTrueRef then ⟨.and, []⟩ else ⟨.or,xs.filterMap liveRef⟩
  | .and => if xs.any isFalseRef then ⟨.or, []⟩ else ⟨.and,xs.filterMap liveRef⟩
  | _ => ⟨.or,[]⟩

lemma wireAll (w : List Bool) (xs : List Ref) :
    (xs.map (evalRef w)).all id =
       (!xs.any isFalseRef && ((xs.filterMap liveRef).map fun j => w.getD j false).all id) := by
  induction xs with
  | nil => rfl
  | cons r xs ih =>
    rcases r with b|j
    · cases b <;> simp [evalRef,isFalseRef,liveRef,ih]
    · simp [evalRef,isFalseRef,liveRef,ih,Bool.and_comm,Bool.and_left_comm]

lemma wireAny (w : List Bool) (xs : List Ref) :
    (xs.map (evalRef w)).any id =
       (xs.any isTrueRef || ((xs.filterMap liveRef).map fun j => w.getD j false).any id) := by
  induction xs with
  | nil => rfl
  | cons r xs ih =>
    rcases r with b|j
    · cases b <;> simp [evalRef,isTrueRef,liveRef,ih]
    · simp [evalRef,isTrueRef,liveRef,ih,Bool.or_comm,Bool.or_left_comm]

lemma shrink_eval (w : List Bool) (o : GateOp) (xs : List Ref)
    (ho : o = .and ∨ o = .or ∨ o = .not) :
    (shrink o xs).op.eval ((shrink o xs).inputs.map fun j => w.getD j false) =
       o.eval (xs.map (evalRef w)) := by
  rcases ho with rfl|rfl|rfl
  · rw [show GateOp.and.eval _ = (xs.map (evalRef w)).all id by rfl, wireAll]
    cases hh : xs.any isFalseRef <;> simp [shrink,GateOp.eval,hh]
  · rw [show GateOp.or.eval _ = (xs.map (evalRef w)).any id by rfl, wireAny]
    cases hh : xs.any isTrueRef <;> simp [shrink,GateOp.eval,hh]
  · cases xs with
    | nil => rfl
    | cons x xs =>
      cases x with
      | inl b => cases b <;> rfl
      | inr i => rfl

lemma shrink_mono (o : GateOp) (xs : List Ref) (h : xs.length ≤ 2) :
    (shrink o xs).op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧
      (shrink o xs).inputs.length ≤ 2 := by
  have h' : (xs.filterMap liveRef).length ≤ 2 := (List.length_filterMap_le liveRef xs).trans h
  cases o with
  | and => by_cases h : xs.any isFalseRef <;> simp [shrink,h,h']
  | or => by_cases h : xs.any isTrueRef <;> simp [shrink,h,h']
  | not =>
    cases xs with
    | nil => simp [shrink]
    | cons r xs =>
      cases r with
      | inl b => cases b <;> simp [shrink]
      | inr i => simp [shrink]
  | mod i => simp [shrink]
  | maj => simp [shrink]

structure Bank where
  gates : List Gate
  names : List Ref

def refAt (s : Bank) (i : Nat) : Ref := s.names.getD i (.inl false)

def init (n : Nat) : Bank := ⟨[], (List.range n).map Sum.inr⟩

def addGate (n : Nat) (s : Bank) (g : Gate) (kill : Option Ref) : Bank :=
  match kill with
  | some (.inl b) => ⟨s.gates,s.names ++ [.inl b]⟩
  | some (.inr j) => ⟨s.gates,s.names ++ [refAt s j]⟩
  | none => ⟨s.gates ++ [shrink g.op (g.inputs.map (refAt s))],
       s.names ++ [.inr (n + s.gates.length)]⟩

@[simp] lemma addGateNamesSize (n : Nat) (s : Bank) (g : Gate) (kill : Option Ref) :
    (addGate n s g kill).names.length = s.names.length + 1 := by
  cases kill with
  | none => simp [addGate]
  | some k => cases k <;> simp [addGate]

lemma addGateSize (n : Nat) (s : Bank) (g : Gate) (kill : Option Ref) :
    (addGate n s g kill).gates.length = s.gates.length + if kill.isSome then 0 else 1 := by
  cases kill with
  | none => simp [addGate]
  | some k => cases k <;> simp [addGate]

def loop (n : Nat) (kill : Nat → Option Ref) (j : Nat) (s : Bank) : List Gate → Bank
  | [] => s
  | g::gs => loop n kill (j+1) (addGate n s g (kill j)) gs


def consistent (s : Bank) (old new : List Bool) : Prop :=
  old.length = s.names.length ∧
    (∀ i, evalRef new (refAt s i) = old.getD i false) ∧
    (∀ i ∈ s.names, ∀ j, i = .inr j → j < new.length)

def appendValue (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map (fun i => w.getD i false))

lemma preserveRef (s : Bank) (old new : List Bool) (h : consistent s old new) (i : Nat) (b : Bool) :
    evalRef (new ++ [b]) (refAt s i) = evalRef new (refAt s i) := by
  generalize hr : refAt s i = q
  cases q with
  | inl b' => rfl
  | inr j =>
    have hj : j < new.length := by
      apply h.2.2 (.inr j) _ j rfl
      by_cases hi : i < s.names.length
      · have he : s.names[i] = Sum.inr j := by
          unfold refAt at hr
          rw [List.getD_eq_getElem _ _ hi] at hr
          exact hr
        rw [← he]; exact List.getElem_mem hi
      · have hn : s.names.length ≤ i := by omega
        unfold refAt at hr
        rw [List.getD_eq_default _ _ hn] at hr
        contradiction
    exact List.getD_append _ _ _ _ hj

lemma add_end {α : Type} (s : List α) (x d : α) (i : Nat) :
    (s ++ [x]).getD i d = if i = s.length then x else s.getD i d := by
  by_cases hi : i < s.length
  · rw [List.getD_append _ _ _ _ hi, ite_eq_right (by omega)]
  · by_cases he : i = s.length
    · subst i; simp
    · have h1 : s.length ≤ i := by omega
      have h2 : (s ++ [x]).length ≤ i := by simp; omega
      rw [ite_eq_right he, List.getD_eq_default _ _ h1, List.getD_eq_default _ _ h2]

lemma newGateEval (s : Bank) (old new : List Bool) (g : Gate) (h : consistent s old new)
    (ho : g.op = .and ∨ g.op = .or ∨ g.op = .not) :
    appendValue new (shrink g.op (g.inputs.map (refAt s))) = appendValue old g := by
  unfold appendValue
  rw [shrink_eval _ _ _ ho, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact h.2.1 i

lemma validCurrent {s : Bank} {w : List Bool}
    (h : ∀ r ∈ s.names, ∀ j, r = .inr j → j < w.length) (i j : Nat)
    (hr : refAt s i = .inr j) : j < w.length := by
  apply h (.inr j) _ j rfl
  by_cases hi : i < s.names.length
  · have hh : s.names[i] = Sum.inr j := by
      unfold refAt at hr
      rw [List.getD_eq_getElem _ _ hi] at hr
      exact hr
    rw [← hh]; exact List.getElem_mem hi
  · have hn : s.names.length ≤ i := by omega
    unfold refAt at hr
    rw [List.getD_eq_default _ _ hn] at hr
    contradiction


def addLiveValues (n : Nat) (s : Bank) (g : Gate) (kill : Option Ref) (new : List Bool) :=
  if kill.isSome then new else new ++ [appendValue new (shrink g.op (g.inputs.map (refAt s)))]

lemma consKeep (n : Nat) (s : Bank) (old new : List Bool) (g : Gate)
    (h : consistent s old new) (hnew : new.length = n + s.gates.length)
    (ho : g.op = .and ∨ g.op = .or ∨ g.op = .not) :
    consistent (addGate n s g none) (old ++ [appendValue old g]) (addLiveValues n s g none new) := by
  let b := appendValue new (shrink g.op (g.inputs.map (refAt s)))
  have eqb : b = appendValue old g := newGateEval s old new g h ho
  change (old ++ [appendValue old g]).length = (s.names ++ [Sum.inr (n + s.gates.length)]).length ∧
    (∀ i, evalRef (new ++ [b]) ((s.names ++ [Sum.inr (n + s.gates.length)]).getD i (.inl false)) =
      (old ++ [appendValue old g]).getD i false) ∧ _
  refine ⟨by simp [h.1], ?_, ?_⟩
  · intro i
    rw [add_end,add_end,h.1]
    by_cases hi : i = s.names.length
    · simp only [hi,ite_eq_left rfl,evalRef,← hnew]
      simp [eqb]
    · simp only [ite_eq_right hi]
      exact (preserveRef s old new h i b).trans (h.2.1 i)
  · intro q hq j hj
    simp only [addGate,List.mem_append,List.mem_singleton] at hq
    rcases hq with hq|rfl
    · have hv := h.2.2 q hq j hj
      simp [addLiveValues]; omega
    · simp only [Sum.inr.injEq] at hj
      simp [addLiveValues]; omega

def resolve (s : Bank) : Ref → Ref
  | .inl b => .inl b
  | .inr i => refAt s i

lemma consKill (n : Nat) (s : Bank) (old new : List Bool) (g : Gate) (mark : Ref)
    (h : consistent s old new)
    (hm : evalRef new (resolve s mark) = appendValue old g) :
    consistent (addGate n s g (some mark)) (old ++ [appendValue old g])
      (addLiveValues n s g (some mark) new) := by
  let q : Ref := resolve s mark
  have eS : addGate n s g (some mark) = ⟨s.gates, s.names ++ [q]⟩ := by
    cases mark <;> rfl
  rw [eS]
  change (old ++ [_]).length = (s.names ++ [q]).length ∧
    (∀ i, evalRef new ((s.names ++ [q]).getD i (.inl false)) = (old ++ [appendValue old g]).getD i false) ∧ _
  refine ⟨by simp [h.1], ?_, ?_⟩
  · intro i
    rw [add_end,add_end,h.1]
    by_cases hi : i = s.names.length
    · rw [ite_eq_left hi, ite_eq_left hi]
      simpa only [q] using hm
    · rw [ite_eq_right hi, ite_eq_right hi]
      exact h.2.1 i
  · intro r hr j hj
    simp only [List.mem_append,List.mem_singleton] at hr
    rcases hr with h0|rfl
    · exact h.2.2 r h0 j hj
    · cases mark with
      | inl x => contradiction
      | inr i => exact validCurrent h.2.2 i j hj


def run (gs : List Gate) (v : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [appendValue w g]) v

lemma run_pres (gs : List Gate) (v : List Bool) (j : Nat) (hj : j < v.length) :
    (run gs v).getD j false = v.getD j false := by
  induction gs generalizing v with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (v ++ [appendValue v g])).getD j false = _
    rw [ih _ (by simp;omega), List.getD_append _ _ _ _ hj]

lemma runLen (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (w ++ [appendValue w g])).length = _
    rw [ih]; simp; omega

lemma runHead (g : Gate) (gs : List Gate) (w : List Bool) :
    (run (g::gs) w).getD w.length false = appendValue w g := by
  change (run gs (w ++ [appendValue w g])).getD w.length false = _
  rw [run_pres _ _ _ (by simp)]
  simp

def Good (kill : Nat → Option Ref) (j : Nat) (gs : List Gate) (old : List Bool) : Prop :=
  ∀ i, i < gs.length →
    let f := run gs old
    match kill (j+i) with
    | none => True
    | some (.inl b) => f.getD (old.length+i) false = b
    | some (.inr w) => w < old.length+i ∧ f.getD (old.length+i) false = f.getD w false

lemma good_tail {kill : Nat → Option Ref} {j : Nat} {g : Gate} {gs : List Gate} {old : List Bool}
    (h : Good kill j (g::gs) old) :
    Good kill (j+1) gs (old ++ [appendValue old g]) := by
  intro i hi
  have he := h (i+1) (by simpa using hi)
  simp only [List.length_append,List.length_singleton] at *
  have hj : j + (i+1) = j+1+i := by omega
  rw [hj] at he
  have hlen : old.length+(i+1) = old.length+1+i := by omega
  rw [hlen] at he
  exact he

lemma good_head {kill : Nat → Option Ref} {j : Nat} {g : Gate} {gs : List Gate} {old : List Bool}
    (h : Good kill j (g::gs) old) (r : Ref) (hr : kill j = some r) :
    (match r with | .inl b => b | .inr w => old.getD w false) = appendValue old g := by
  have hh := h 0 (by simp)
  simp only [Nat.add_zero, hr] at hh
  cases r with
  | inl b =>
    change (run (g::gs) old).getD old.length false = b at hh
    rw [runHead] at hh
    exact hh.symm
  | inr w =>
    change w < old.length ∧
      (run (g::gs) old).getD old.length false = (run (g::gs) old).getD w false at hh
    rw [runHead,run_pres _ _ _ hh.1] at hh
    exact hh.2.symm


lemma loopConsistent (n : Nat) (kill : Nat → Option Ref) (j : Nat)
    (s : Bank) (gs : List Gate) (old new : List Bool)
    (hmono : ∀ g ∈ gs, g.op = .and ∨ g.op = .or ∨ g.op = .not)
    (hgood : Good kill j gs old) (hc : consistent s old new)
    (hn : new = run s.gates (new.take n)) (hi : n ≤ new.length)
    (hlen : new.length = n + s.gates.length) :
    consistent (loop n kill j s gs) (run gs old)
      (run (loop n kill j s gs).gates (new.take n)) := by
  induction gs generalizing j s old new with
  | nil =>
    change consistent s old (run s.gates (new.take n))
    rw [← hn]
    exact hc
  | cons g gs ih =>
    let N := addGate n s g (kill j)
    let v := addLiveValues n s g (kill j) new
    have hv : v = run N.gates (new.take n) := by
      cases hk : kill j with
      | none =>
        change addLiveValues n s g (kill j) new = run (addGate n s g (kill j)).gates _
        simp only [hk,addLiveValues,Option.isSome_none, Bool.false_eq_true, ite_eq_right,
          addGate,run,List.foldl_append,List.foldl_cons,List.foldl_nil]
        exact congrArg (fun w => w ++ [appendValue w (shrink g.op (g.inputs.map (refAt s)))]) hn
      | some m =>
        cases m <;> simpa [v,N,hk,addLiveValues,addGate] using hn
    have ht : v.take n = new.take n := by
      change (addLiveValues n s g (kill j) new).take n = _
      cases hk : kill j <;> simp [addLiveValues,hk,List.take_append,hi]
    have hvl : v.length = n + N.gates.length := by
      rw [hv,runLen,List.length_take,Nat.min_eq_left hi]
    have hcn : consistent N (old ++ [appendValue old g]) v := by
      change consistent (addGate n s g (kill j)) _ (addLiveValues n s g (kill j) new)
      cases hk : kill j with
      | none => simpa [hk] using consKeep n s old new g hc hlen (hmono g List.mem_cons_self)
      | some m =>
        have hm := good_head hgood m hk
        have he : evalRef new (resolve s m) =
            appendValue old g := by
          cases m with
          | inl b => exact hm
          | inr i => exact (hc.2.1 i).trans hm
        simpa [hk] using consKill n s old new g m hc he
    have H := ih (j+1) N (old ++ [appendValue old g]) v
      (fun g hg => hmono g (List.mem_cons_of_mem _ hg)) (good_tail hgood) hcn
      (by rw [ht]; exact hv) (by omega) hvl
    rw [ht] at H
    exact H


def killedCount (kill : Nat → Option Ref) (j g : Nat) : Nat :=
  ((List.range' j g).filter (fun i => (kill i).isSome)).length

theorem loopSize (n : Nat) (kill : Nat → Option Ref) (j : Nat)
    (s : Bank) (gs : List Gate) :
    (loop n kill j s gs).gates.length + killedCount kill j gs.length =
       s.gates.length + gs.length := by
  induction gs generalizing j s with
  | nil => simp [loop,killedCount]
  | cons g gs ih =>
    have he := ih (j+1) (addGate n s g (kill j))
    simp only [addGateSize] at he
    simp only [loop,List.length_cons,killedCount,List.range'_succ,List.filter_cons]
    unfold killedCount at he
    cases hk : kill j <;> simp [hk] at * <;> omega

theorem loopFan (n : Nat) (kill : Nat → Option Ref) (j : Nat)
    (s : Bank) (gs : List Gate)
    (hs : FanInTwo ⟨s.gates,0⟩) (hg : FanInTwo ⟨gs,0⟩) :
    FanInTwo ⟨(loop n kill j s gs).gates,0⟩ := by
  induction gs generalizing j s with
  | nil => exact hs
  | cons g gs ih =>
    simp only [loop]
    apply ih
    · intro a ha
      change a ∈ (addGate n s g (kill j)).gates at ha
      have hlen := (hg g List.mem_cons_self).2
      cases hk : kill j with
      | none =>
        simp only [hk,addGate,List.mem_append,List.mem_singleton] at ha
        rcases ha with ha|rfl
        · exact hs a ha
        · exact shrink_mono _ _ (by simpa using hlen)
      | some r =>
        cases r <;> exact hs a (by simpa [hk,addGate] using ha)
    · intro a ha
      exact hg a (List.mem_cons_of_mem _ ha)


lemma refAt_init (n i : Nat) :
    refAt (init n) i = if i < n then .inr i else .inl false := by
  simp only [refAt,init,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range]
  by_cases h : i < n <;> simp [h]

lemma init_consistent (v : List Bool) : consistent (init v.length) v v := by
  refine ⟨by simp [init], ?_, ?_⟩
  · intro i
    rw [refAt_init]
    by_cases h : i < v.length
    · simp [h,evalRef]
    · simp only [ite_eq_right h,evalRef]
      symm; exact List.getD_eq_default _ _ (by omega)
  · intro r hr i hi
    subst r
    change Sum.inr i ∈ (List.range v.length).map Sum.inr at hr
    simpa using hr

lemma names_extend (n : Nat) (s : Bank) (g : Gate) (k : Option Ref) :
    ∃ r, (addGate n s g k).names = s.names ++ [r] := by
  cases k with
  | none => exact ⟨_, rfl⟩
  | some r => cases r <;> exact ⟨_,rfl⟩

lemma loopNamesLen (n : Nat) (k : Nat → Option Ref) (j : Nat) (s : Bank) (gs : List Gate) :
    (loop n k j s gs).names.length = s.names.length + gs.length := by
  induction gs generalizing j s with
  | nil => simp [loop]
  | cons g gs ih =>
    simp only [loop,ih,addGateNamesSize,List.length_cons]
    omega

lemma loopRef_pres (n : Nat) (k : Nat → Option Ref) (j : Nat) (s : Bank) (gs : List Gate)
    (i : Nat) (hi : i < s.names.length) :
    refAt (loop n k j s gs) i = refAt s i := by
  induction gs generalizing j s with
  | nil => rfl
  | cons g gs ih =>
    simp only [loop]
    rw [ih _ _ (by simp;omega)]
    obtain ⟨r,hr⟩ := names_extend n s g (k j)
    unfold refAt
    rw [hr,List.getD_append _ _ _ _ hi]

lemma loopRef_live (n : Nat) (k : Nat → Option Ref) (j : Nat) (s : Bank) (gs : List Gate)
    (i : Nat) (hi : i < gs.length) (hk : k (j+i) = none) :
    ∃ w, refAt (loop n k j s gs) (s.names.length+i) = .inr w := by
  induction gs generalizing j s i with
  | nil => simp at hi
  | cons g gs ih =>
    cases i with
    | zero =>
      simp only [Nat.add_zero] at hk ⊢
      simp only [loop]
      rw [loopRef_pres _ _ _ _ _ _ (by simp)]
      refine ⟨n+s.gates.length, ?_⟩
      simp [refAt,addGate,hk]
    | succ i =>
      simp only [loop]
      have he : j + (i+1) = j+1+i := by omega
      rw [he] at hk
      obtain ⟨r,hr⟩ := ih (j+1) (addGate n s g (k j)) i (by simpa using hi) hk
      refine ⟨r,?_⟩
      rw [addGateNamesSize] at hr
      rwa [show s.names.length + (i+1) = s.names.length + 1 + i by omega]


def initFix (n w : Nat) (b : Bool) : Bank :=
  ⟨[], (List.range n).map (fun i => if i = w then .inl b else .inr i)⟩

lemma refAt_initFix (n w i : Nat) (b : Bool) :
    refAt (initFix n w b) i =
      if i < n then if i = w then .inl b else .inr i else .inl false := by
  simp only [refAt,initFix,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range]
  by_cases h : i < n <;> simp [h]

lemma initFix_ok {n : Nat} (v : Fin n) (b : Bool) (x : Fin n → Bool) :
    consistent (initFix n v.val b) (List.ofFn (Function.update x v b)) (List.ofFn x) := by
  refine ⟨by simp [initFix], ?_, ?_⟩
  · intro i
    rw [refAt_initFix]
    by_cases hi : i < n
    · rw [ite_eq_left hi]
      rw [List.getD_eq_getElem _ _ (by simpa using hi)]
      by_cases hv : i = v.val
      · rw [ite_eq_left hv]
        have E : (⟨i,hi⟩ : Fin n) = v := Fin.ext hv
        simp [evalRef,E]
      · rw [ite_eq_right hv]
        have E : (⟨i,hi⟩ : Fin n) ≠ v := fun h => hv (congrArg Fin.val h)
        change (List.ofFn x).getD i false = _
        rw [List.getD_eq_getElem _ _ (by simpa using hi)]
        simp [Function.update_of_ne E]
    · rw [ite_eq_right hi, List.getD_eq_default _ _ (by simp;omega)]
      rfl
  · intro r hr i hi
    have hh := List.mem_map.mp hr
    obtain ⟨a,ha,E⟩ := hh
    rw [hi] at E
    by_cases e : a = v.val
    · simp [e] at E
    · simp [e] at E
      subst i
      simpa using ha

def chooseAlias (bound : Nat) (o : Option Nat) (neutral : Bool) : Ref :=
  match o with
  | none => .inl neutral
  | some w => if w < bound then .inr w else .inl false

def markDirect (bound v : Nat) (b : Bool) (g : Gate) : Ref :=
  let others := (g.inputs.filter fun j => j != v).head?
  match g.op with
  | .not => .inl (!b)
  | .and => if b then chooseAlias bound others true else .inl false
  | .or => if b then .inl true else chooseAlias bound others false
  | _ => .inl false

@[simp] lemma alias_none (w : List Bool) (b : Bool) :
    evalRef w (chooseAlias w.length none b) = b := rfl

lemma alias_ok (w : List Bool) (i : Nat) (z : Bool) :
    evalRef w (chooseAlias w.length (some i) z) = w.getD i false := by
  by_cases h : i < w.length
  · simp [chooseAlias,evalRef,h]
  · simp [chooseAlias,evalRef,h,List.getD_eq_default _ _ (by omega : w.length ≤ i)]

lemma choose_bound (n : Nat) (o : Option Nat) (b : Bool) :
    match chooseAlias n o b with | .inl _ => True | .inr j => j < n := by
  cases o with
  | none => trivial
  | some w => by_cases h : w < n <;> simp [chooseAlias,h]

lemma usefulAlias (w : List Bool) (v : Nat) (b : Bool) (g : Gate) :
    match markDirect w.length v b g with | .inl _ => True | .inr j => j < w.length := by
  obtain ⟨op,args⟩ := g
  cases op <;> cases b <;> simp [markDirect] <;> exact choose_bound _ _ _

lemma mark_sound (w : List Bool) (v : Nat) (b : Bool) (g : Gate)
    (hv : w.getD v false = b) (hm : v ∈ g.inputs) (hl : g.inputs.length ≤ 2)
    (ho : g.op = .and ∨ g.op = .or ∨ g.op = .not)
    (hnot : g.op = .not → g.inputs.length = 1) :
    evalRef w (markDirect w.length v b g) = appendValue w g := by
  obtain ⟨o,args⟩ := g
  have hv' : w[v]?.getD false = b := by rwa [← List.getD_eq_getElem?_getD]
  change o = .and ∨ o = .or ∨ o = .not at ho
  change v ∈ args at hm
  change args.length ≤ 2 at hl
  change o = .not → args.length = 1 at hnot
  cases args with
  | nil => simp at hm
  | cons a t =>
    cases t with
    | nil =>
      have eq : a = v := by simpa [eq_comm] using hm
      subst a
      rcases ho with rfl|rfl|rfl <;> cases b <;>
        simp [markDirect,chooseAlias,appendValue,GateOp.eval,evalRef,hv,hv']
    | cons d t =>
      have hnil : t = [] := by
        apply List.length_eq_zero_iff.mp; simp only [List.length_cons] at hl; omega
      subst t
      have eq : v = a ∨ v = d := by simpa using hm
      rcases ho with rfl|rfl|rfl
      · rcases eq with hv1|hv2
        · subst a
          by_cases h : d = v <;> cases b <;>
            simp [markDirect,appendValue,GateOp.eval,evalRef,hv,hv',h,alias_ok] <;> first | rfl | exact alias_ok _ _ _
        · subst d
          by_cases h : a = v <;> cases b <;>
            simp [markDirect,appendValue,GateOp.eval,evalRef,hv,hv',h,alias_ok] <;> first | rfl | exact alias_ok _ _ _
      · rcases eq with hv1|hv2
        · subst a
          by_cases h : d = v <;> cases b <;>
            simp [markDirect,appendValue,GateOp.eval,evalRef,hv,hv',h,alias_ok] <;> first | rfl | exact alias_ok _ _ _
        · subst d
          by_cases h : a = v <;> cases b <;>
            simp [markDirect,appendValue,GateOp.eval,evalRef,hv,hv',h,alias_ok] <;> first | rfl | exact alias_ok _ _ _
      · have H := hnot rfl
        simp at H

lemma runAt (gs : List Gate) (old : List Bool) (j : Nat) (hj : j < gs.length) :
    (run gs old).getD (old.length+j) false = appendValue (run (gs.take j) old) gs[j] := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j+1) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have hlen : (run (gs.take j) old).length = old.length+j := by
    simp [runLen,List.length_take,Nat.min_eq_left (Nat.le_of_lt hj)]
  conv_lhs => rw [hsplit]
  rw [← hlen]
  unfold run
  rw [List.foldl_append]
  change (run (gs[j] :: gs.drop (j+1)) (run (gs.take j) old)).getD
    (run (gs.take j) old).length false = _
  exact runHead _ _ _

lemma runEarlier (gs : List Gate) (old : List Bool) (j i : Nat) (hj : j ≤ gs.length)
    (hi : i < old.length+j) :
    (run gs old).getD i false = (run (gs.take j) old).getD i false := by
  have hs := (List.take_append_drop j gs).symm
  have hlen : (run (gs.take j) old).length = old.length+j := by
    simp [runLen,List.length_take,Nat.min_eq_left hj]
  conv_lhs => rw [hs]
  unfold run
  rw [List.foldl_append]
  change (run (gs.drop j) (run (gs.take j) old)).getD i false = _
  exact run_pres _ _ _ (by omega)

end PEqualNP.Outside.L_meta_18350


open PEqualNP.Outside.L_meta_18350 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_18350 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin n) (b : Bool), PEqualNP.MetaComplexity.FanInTwo C → (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.length = 1) → (∃ y : Fin n → Bool, C.eval (List.ofFn (Function.update y v b)) = false) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size + (Finset.univ.filter (fun j : Fin C.gates.length => v.val ∈ (C.gates.get j).inputs)).card ≤ C.size ∧ ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x v b)) := by
  intro n C v b hfan hnot hnon
  classical
  let kill (j : Nat) : Option Ref :=
    (C.gates[j]?).bind (fun g => if v.val ∈ g.inputs then some (markDirect (n+j) v.val b g) else none)
  let initB := initFix n v.val b
  let S := loop n kill 0 initB C.gates
  let o := match refAt S C.output with | .inr r => r | .inl _ => n+S.gates.length
  let D : Circuit := ⟨S.gates,o⟩
  have hD : FanInTwo D := loopFan n kill 0 initB C.gates (by simp [FanInTwo,initB,initFix]) hfan
  have hcOp (g : Gate) (hg : g ∈ C.gates) : g.op = .and ∨ g.op = .or ∨ g.op = .not := by
    simpa using (hfan g hg).1
  have hgood (x : Fin n → Bool) :
      Good kill 0 C.gates (List.ofFn (Function.update x v b)) := by
    let raw := List.ofFn (Function.update x v b)
    have rl : raw.length = n := by simp [raw]
    intro i hi
    by_cases hm : v.val ∈ C.gates[i].inputs
    · simp only [Nat.zero_add,kill,List.getElem?_eq_getElem hi,Option.bind_some,ite_eq_left hm]
      change (match some (markDirect (n+i) v.val b C.gates[i]) with
          | none => True
          | some (.inl z) => (run C.gates raw).getD (raw.length+i) false = z
          | some (.inr w) => w < raw.length+i ∧
            (run C.gates raw).getD (raw.length+i) false = (run C.gates raw).getD w false)
      let pre := run (C.gates.take i) raw
      have hp : pre.length = n+i := by
        simp [pre,runLen,rl,List.length_take,Nat.min_eq_left (Nat.le_of_lt hi)]
      have hx : pre.getD v.val false = b := by
        change (run (C.gates.take i) raw).getD v.val false = b
        rw [run_pres _ _ _ (by rw [rl]; exact v.isLt)]
        have hvn : v.val < raw.length := by rw [rl]; exact v.isLt
        rw [List.getD_eq_getElem _ _ hvn]
        simp [raw]
      have he := mark_sound pre v.val b C.gates[i] hx hm
        (hfan _ (List.getElem_mem hi)).2 (hcOp _ (List.getElem_mem hi))
        (hnot _ (List.getElem_mem hi))
      have hu := usefulAlias pre v.val b C.gates[i]
      rw [hp] at he hu
      have ev := runAt C.gates raw i hi
      change (run C.gates raw).getD (raw.length+i) false = appendValue pre C.gates[i] at ev
      cases hr : markDirect (n+i) v.val b C.gates[i] with
      | inl z =>
        rw [hr] at he
        exact ev.trans he.symm
      | inr w =>
        rw [hr] at he hu
        change w < n+i at hu
        have hw : w < raw.length+i := by omega
        refine ⟨hw,ev.trans ?_⟩
        rw [runEarlier C.gates raw i w (Nat.le_of_lt hi) hw]
        exact he.symm
    · simp [kill,List.getElem?_eq_getElem hi,hm]
  have bank (x : Fin n → Bool) :
      consistent S (C.wires (List.ofFn (Function.update x v b))) (D.wires (List.ofFn x)) := by
    have he := loopConsistent n kill 0 initB C.gates _ (List.ofFn x) hcOp (hgood x)
      (initFix_ok v b x) (by simp [initB,initFix,run]) (by simp) (by simp [initB,initFix])
    change consistent S (run C.gates (List.ofFn (Function.update x v b))) (run S.gates (List.ofFn x))
    simpa only [List.take_of_length_le (by simp : (List.ofFn x).length ≤ n)] using he
  let F := (Finset.univ : Finset (Fin C.gates.length)).filter
    (fun j => v.val ∈ (C.gates.get j).inputs)
  let L := (List.range' 0 C.gates.length).filter (fun j => (kill j).isSome)
  let emb : Fin C.gates.length ↪ Nat := ⟨Fin.val,Fin.val_injective⟩
  have hKL : L.toFinset = F.map emb := by
    ext j
    simp only [L, List.mem_toFinset,List.mem_filter,Finset.mem_map,F,Finset.mem_filter,
      Finset.mem_univ,true_and]
    by_cases hj : j < C.gates.length
    · have ht : j ∈ List.range' 0 C.gates.length := by simp [List.mem_range',hj]
      simp only [ht,true_and,kill,List.getElem?_eq_getElem hj,Option.bind_some]
      by_cases hM : v.val ∈ C.gates[j].inputs
      · refine ⟨fun _ => ⟨⟨j,hj⟩,hM,rfl⟩,fun _ => ?_⟩
        simp [hM]
      · simp only [ite_eq_right hM,Option.isSome_none,Bool.false_eq_true,false_iff]
        rintro ⟨a,ha,hv⟩
        have ee : a = (⟨j,hj⟩ : Fin C.gates.length) := Fin.ext hv
        subst a
        exact hM ha
    · constructor
      · rintro ⟨ha,_⟩
        simp [List.mem_range'] at ha
        omega
      · rintro ⟨a,ha,he⟩
        have h := a.isLt
        change a.val = j at he
        omega
  have hs : killedCount kill 0 C.gates.length = F.card := by
    change L.length = F.card
    have nd : L.Nodup := (List.nodup_range' _).filter _
    rw [← List.toFinset_card_of_nodup nd,hKL,Finset.card_map]
  have hsz : D.size + F.card ≤ C.size := by
    change S.gates.length + F.card ≤ C.gates.length
    rw [← hs]
    apply le_of_eq
    simpa only [S,initB,initFix,List.length_nil,Nat.zero_add] using loopSize n kill 0 initB C.gates
  have hnever : refAt S C.output ≠ .inl true := by
    obtain ⟨y,hy⟩ := hnon
    have he := (bank y).2.1 C.output
    change evalRef (D.wires (List.ofFn y)) (refAt S C.output) = C.eval (List.ofFn (Function.update y v b)) at he
    intro hc
    rw [hc,hy] at he
    contradiction
  refine ⟨D,hD,hsz,?_⟩
  intro x
  have hrec := (bank x).2.1 C.output
  have he : D.eval (List.ofFn x) = evalRef (D.wires (List.ofFn x)) (refAt S C.output) := by
    cases rr : refAt S C.output with
    | inr w => simp [D,o,rr,evalRef,Circuit.eval]
    | inl z =>
      cases z
      · change (run S.gates (List.ofFn x)).getD o false = false
        have oo : o = n+S.gates.length := by simp [o,rr]
        rw [oo,List.getD_eq_default]
        simp [runLen]
      · exact False.elim (hnever rr)
  exact he.trans hrec
