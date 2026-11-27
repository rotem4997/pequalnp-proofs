import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18804
namespace Peter17
def target (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def signed (b w : Bool) := if b then !w else w

end Peter17
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Reader7354
def pins (g : Gate) := match g.op with | .not => g.inputs.take 1 | _ => g.inputs
def touch (g : Gate) : Bool := (pins g).any (fun i => i == 0 || i == 10)
def spec (C : Circuit) := ∀ x : Fin 10 → Bool,
  C.eval (List.ofFn x ++ [x 0 && x 2]) = Peter17.target x
def pinFloor := ∀ (D : Circuit), FanInTwo D → D.size ≤ 15 →
  ∃ x : Fin 10 → Bool, x 0=false ∧ D.eval (List.ofFn x) ≠ Peter17.target x
end Reader7354

namespace Reader7354.Copy
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def name {n m} (f : Fin n → Fin m) (base i : ℕ) :=
  if hi : i<n then (f ⟨i,hi⟩).val else base+(i-n)
def renameG {n m} (f : Fin n → Fin m) (base : ℕ) (g : Gate) : Gate :=
  ⟨g.op,g.inputs.map (name f base)⟩
theorem name_lt {n m} (f : Fin n → Fin m) {base j i : ℕ} (hb : m≤base) (hi : i<n+j) :
    name f base i < base+j := by
  unfold name
  split
  next h => have := (f ⟨i,h⟩).isLt; omega
  next => omega

def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def run (gs : List Gate) (w : List Bool) := gs.foldl step w
theorem len (gs : List Gate) (w : List Bool) : (run gs w).length = w.length+gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (step w g)).length = _
    rw [ih]; simp [step]; omega
theorem old (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k<w.length) : (run gs w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD k false = _
    rw [ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hk

theorem lookup {n m} (f : Fin n → Fin m) (W : List Bool) (hw : m ≤ W.length)
    (x : Fin n → Bool) (ag : ∀ p, W.getD (f p).val false = x p) (z : List Bool) (i : Nat) :
    (W++z).getD (name f W.length i) false = (List.ofFn x++z).getD i false := by
  unfold name
  split
  next hi =>
    rw [List.getD_append _ _ _ _ (by have := (f ⟨i,hi⟩).isLt; omega),List.getD_append _ _ _ _ (by simpa)]
    simpa [List.getD,hi] using ag ⟨i,hi⟩
  next hi =>
    simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega : W.length ≤ W.length+(i-n)),
      List.getElem?_append_right (by simp;omega : (List.ofFn x).length ≤ i),List.length_ofFn,Nat.add_sub_cancel_left]

theorem sim {n m} (f : Fin n → Fin m) (W : List Bool) (hw : m≤W.length)
    (x : Fin n → Bool) (ag : ∀ p, W.getD (f p).val false = x p) (gs : List Gate) (z : List Bool) :
    ∃ endBits, run gs (List.ofFn x ++ z) = List.ofFn x ++ endBits ∧
      run (gs.map (renameG f W.length)) (W++z) = W++endBits := by
  induction gs generalizing z with
  | nil => exact ⟨z,rfl,rfl⟩
  | cons g gs ih =>
    let bit := g.op.eval (g.inputs.map fun i => (List.ofFn x ++ z).getD i false)
    obtain ⟨t,h1,h2⟩ := ih (z++[bit])
    refine ⟨t,?_,?_⟩
    · simpa [run,step,bit,List.append_assoc] using h1
    · have hstep : step (W++z) (renameG f W.length g) = W++(z++[bit]) := by
        simp only [step,renameG,List.map_map,Function.comp_def,lookup f W hw x ag,List.append_assoc,bit]
      change run _ (step (W++z) (renameG f W.length g)) = _
      rw [hstep];exact h2

theorem copy_val {n m} (f : Fin n → Fin m) (W : List Bool) (hw : m≤W.length)
    (x : Fin n → Bool) (ag : ∀ p, W.getD (f p).val false = x p) (C : Circuit) :
    (run (C.gates.map (renameG f W.length)) W).getD (name f W.length C.output) false = circuitFun n C x := by
  obtain ⟨z,h1,h2⟩ := sim f W hw x ag C.gates []
  simp only [List.append_nil] at h1 h2
  change _ = (run C.gates (List.ofFn x)).getD C.output false
  rw [h1,h2,lookup _ _ hw x ag]

end Reader7354.Copy
namespace Reader7354
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def rawShrink (i : Fin 11) : Fin 10 := if h : i.val<10 then ⟨i.val,h⟩ else 0
def collapse := Copy.name rawShrink 10
def down (g : Gate) : Gate := ⟨g.op,g.inputs.map collapse⟩
def squeeze (C : Circuit) : Circuit := ⟨C.gates.map down, collapse C.output⟩
theorem collapse_zero_iff (i : ℕ) : collapse i=0 ↔ i=0 ∨ i=10 := by
  by_cases h : i<10
  · have h' : i<11 := by omega
    simp [collapse, Copy.name, rawShrink,h,h']; omega
  · by_cases h' : i<11
    · have : i=10 := by omega
      subst i; decide
    · simp [collapse,Copy.name,h']; omega
theorem squeeze_size (C : Circuit) : (squeeze C).size=C.size := by simp [squeeze,Circuit.size]
theorem squeeze_fan (C : Circuit) (h : FanInTwo C) : FanInTwo (squeeze C) := by
  intro g hg
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hg
  simpa [down] using h v hv
theorem squeeze_eval (C : Circuit) (x : Fin 10→Bool) :
    (squeeze C).eval (List.ofFn x) = C.eval (List.ofFn x ++ [x 0]) := by
  have ag (p : Fin 11) : (List.ofFn x).getD (rawShrink p).val false = (x ∘ rawShrink) p := by
    fin_cases p <;> rfl
  have hl : List.ofFn (x ∘ rawShrink) = List.ofFn x ++ [x 0] := rfl
  have h := Copy.copy_val rawShrink (List.ofFn x) (by simp) (x ∘ rawShrink) ag C
  simp only [List.length_ofFn] at h
  rw [←hl]
  exact h
end Reader7354

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Reader7354
def fixG (g : Gate) : Gate :=
  if 0 ∈ pins g ∧ 10 ∈ pins g then
    match g.op with | .and => ⟨.and,[10]⟩ | _ => ⟨.or,[0]⟩
  else ⟨g.op,pins g⟩
def fixed (C : Circuit) : Circuit := ⟨C.gates.map fixG,C.output⟩
def gval (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
theorem pair {l : List ℕ} (n : l.length≤2) (h : 0∈l ∧ 10∈l) :
    l=[0,10] ∨ l=[10,0] := by
  rcases l with _|⟨a, l⟩
  · simp at h
  rcases l with _|⟨b,l⟩
  · simp_all <;> omega
  rcases l with _|⟨c,l⟩
  · simp at h
    grind
  · simp at n
theorem sep (g : Gate) : ¬ (0∈(fixG g).inputs ∧ 10∈(fixG g).inputs) := by
  unfold fixG
  split
  · rcases g with ⟨op,l⟩; cases op <;> simp
  · assumption
theorem touch_of_fix (g : Gate) (h : 0∈(fixG g).inputs ∨ 10∈(fixG g).inputs) : touch g = true := by
  rw [touch,List.any_eq_true]
  have one : 0∈pins g ∨ 10∈pins g := by
    unfold fixG at h
    split at h
    next both => exact Or.inl both.1
    next => exact h
  rcases one with h|h
  · exact ⟨0,h,rfl⟩
  · exact ⟨10,h,rfl⟩
theorem pins_len (g : Gate) : (pins g).length ≤ g.inputs.length := by
  rcases g with ⟨op,l⟩; cases op <;> simp [pins,List.length_take]
theorem fix_fan (C : Circuit) (fan : FanInTwo C) : FanInTwo (fixed C) := by
  intro g hg
  obtain ⟨h,hm,rfl⟩ := List.mem_map.mp hg
  have hx := fan h hm
  unfold fixG
  split
  · cases h with | mk op l => cases op <;> simp
  · exact ⟨hx.1,(pins_len h).trans hx.2⟩
theorem fix_size (C : Circuit) : (fixed C).size = C.size := by simp [fixed,Circuit.size]

theorem evalPins (g : Gate) (w : List Bool) : gval ⟨g.op,pins g⟩ w = gval g w := by
  rcases g with ⟨op,l⟩
  cases op <;> first | rfl | (cases l <;> rfl)

theorem fix_val (g : Gate) (fan : g.op∈({.and,.or,.not} : Set GateOp) ∧ g.inputs.length≤2)
    (w : List Bool) (a b : Bool) (h0 : w.getD 0 false=a) (h10 : w.getD 10 false = (a && b)) :
    gval (fixG g) w = gval g w := by
  rw [←evalPins g w]
  unfold fixG
  split
  next hb =>
    have hp := pair ((pins_len g).trans fan.2) hb
    rcases hp with hp|hp
    all_goals
      rw [hp]
      rcases g with ⟨op,l⟩
      cases op <;> simp_all [gval,GateOp.eval,pins,Set.mem_insert_iff]
    all_goals first | (cases a <;> cases b <;> simp_all) |
      (have := congrArg List.length hp; simp [List.length_take] at this; omega)
    all_goals have q := congrArg List.length hp; simp only [List.length_take,List.length_cons,List.length_nil] at q; omega
  next => rfl

theorem fixed_eval (C : Circuit) (fan : FanInTwo C) (x : Fin 10→Bool) :
    (fixed C).eval (List.ofFn x ++ [x 0 && x 2]) = C.eval (List.ofFn x ++ [x 0 && x 2]) := by
  have fk (gs : List Gate) (legal : ∀g∈gs,g.op∈({.and,.or,.not}:Set GateOp) ∧ g.inputs.length≤2) :
      ∀ (w : List Bool), 10<w.length → w.getD 0 false=x 0 → w.getD 10 false=(x 0 && x 2) →
      Copy.run (gs.map fixG) w = Copy.run gs w := by
    induction gs with
    | nil => intros; rfl
    | cons g gs ih =>
      intro w len h0 hz
      have h := fix_val g (legal g List.mem_cons_self) w (x 0) (x 2) h0 hz
      change Copy.run (gs.map fixG) (w++[gval (fixG g) w]) = Copy.run gs (w++[gval g w])
      rw [h]
      apply ih (fun j hj => legal j (List.mem_cons_of_mem _ hj))
      · simp; omega
      · rwa [List.getD_append _ _ _ _ (by omega)]
      · rwa [List.getD_append _ _ _ _ len]
  exact congrArg (fun w : List Bool => w.getD C.output false) (fk C.gates fan _ (by simp) rfl rfl)

theorem ignore (gs : List Gate) (idx : ℕ) (no : ∀g∈gs, idx∉g.inputs) :
    ∀ w v : List Bool, w.length=v.length → (∀i,i≠idx → w.getD i false = v.getD i false) →
    ∀i,i≠idx → (Copy.run gs w).getD i false=(Copy.run gs v).getD i false := by
  induction gs with
  | nil => exact fun w v _ h => h
  | cons g gs ih =>
    intro w v len eq
    have same : gval g w = gval g v := congrArg g.op.eval
      (List.map_congr_left (fun i hi => eq i (fun e => no g List.mem_cons_self (e ▸ hi))))
    change ∀i, i≠idx → (Copy.run gs (w++[gval g w])).getD i false = (Copy.run gs (v++[gval g v])).getD i false
    rw [same]
    apply ih (fun g hg => no g (List.mem_cons_of_mem _ hg)) _ _ (by simp [len])
    intro i hi
    by_cases hlt : i < w.length
    · rw [List.getD_append _ _ _ _ hlt,List.getD_append _ _ _ _ (by omega)]
      exact eq i hi
    · simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega : w.length ≤ i),
        List.getElem?_append_right (by omega : v.length ≤ i),len]
end Reader7354

namespace Reader7354
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem no_pins (C : Circuit) (few : C.gates.countP touch ≤ 1) :
    (∀g∈(fixed C).gates, 0∉g.inputs) ∨ (∀g∈(fixed C).gates, 10∉g.inputs) := by
  by_contra! bad
  rcases bad with ⟨⟨g,hg,h0⟩,⟨h,hh,h10⟩⟩
  obtain ⟨g₀,hg₀,rfl⟩ := List.mem_map.mp hg
  obtain ⟨h₀,hh₀,rfl⟩ := List.mem_map.mp hh
  let pool := C.gates.filter touch
  have gmem : g₀ ∈ pool := List.mem_filter.mpr ⟨hg₀,touch_of_fix g₀ (Or.inl h0)⟩
  have hmem : h₀ ∈ pool := List.mem_filter.mpr ⟨hh₀,touch_of_fix h₀ (Or.inr h10)⟩
  have hp : pool.length ≤ 1 := by simpa only [pool,List.countP_eq_length_filter] using few
  have unique (l : List Gate) (hl : l.length ≤ 1) (g h : Gate) (g₁ : g∈l) (h₁ : h∈l) : g=h := by
    cases l with
    | nil => simp at g₁
    | cons v t =>
      cases t with
      | nil => simp_all
      | cons y r => simp at hl
  have geq := unique pool hp g₀ h₀ gmem hmem
  subst h₀
  exact sep g₀ ⟨h0,h10⟩

theorem out_ne (C : Circuit) (ok : spec C) : C.output ≠ 0 ∧ C.output ≠ 10 := by
  let x : Fin 10 → Bool := fun i => decide (i.val=3 ∨ i.val=4)
  let w := List.ofFn x ++ [x 0 && x 2]
  have h := ok x
  change (Copy.run C.gates w).getD C.output false = Peter17.target x at h
  have ht : Peter17.target x=true := rfl
  rw [ht] at h
  constructor
  · rintro e
    rw [e,Copy.old _ _ _ (by simp [w])] at h
    exact Bool.noConfusion h
  · rintro e
    rw [e,Copy.old _ _ _ (by simp [w])] at h
    exact Bool.noConfusion h

theorem no0_absurd (C : Circuit) (ok : spec C) (no : ∀g∈C.gates,0∉g.inputs) : False := by
  let a : Fin 10 → Bool := fun i => decide (i.val=1)
  let b : Fin 10 → Bool := fun i => decide (i.val≤1)
  let w := List.ofFn a ++ [a 0 && a 2]
  let v := List.ofFn b ++ [b 0 && b 2]
  have neq : C.output ≠ 0 := (out_ne C ok).1
  have src (i : ℕ) (hn : i≠0) : w.getD i false=v.getD i false := by
    by_cases h : i<11
    · interval_cases i <;> first | contradiction | rfl
    · rw [List.getD_eq_default _ _ (by simp [w];omega),List.getD_eq_default _ _ (by simp [v];omega)]
  have agree := ignore C.gates 0 no w v (by simp [w,v]) src C.output neq
  have h1 := ok a
  have h2 := ok b
  change (Copy.run C.gates w).getD C.output false = Peter17.target a at h1
  change (Copy.run C.gates v).getD C.output false = Peter17.target b at h2
  rw [h1,h2] at agree
  exact Bool.noConfusion agree

def ordinary17 := ∀ C : Circuit, FanInTwo C → C.size≤17 →
  ∃ x : Fin 10→Bool, C.eval (List.ofFn x) ≠ Peter17.target x

theorem noz_absurd (floor : ordinary17) (C : Circuit) (fan : FanInTwo C) (small : C.size ≤ 17)
    (ok : spec C) (no : ∀g∈C.gates,10∉g.inputs) : False := by
  obtain ⟨x,hx⟩ := floor (squeeze C) (squeeze_fan C fan) (by rwa [squeeze_size])
  apply hx
  rw [squeeze_eval]
  let a := List.ofFn x ++ [x 0]
  let b := List.ofFn x ++ [x 0 && x 2]
  have agree (i : ℕ) (hi : i≠10) : a.getD i false=b.getD i false := by
    by_cases small : i<10
    · exact (List.getD_append _ _ _ _ (by simpa using small)).trans
        (List.getD_append _ _ _ _ (by simpa using small)).symm
    · rw [List.getD_eq_default _ _ (by simp [a];omega),List.getD_eq_default _ _ (by simp [b];omega)]
  exact (ignore C.gates 10 no a b (by simp [a,b]) agree C.output (out_ne C ok).2).trans (ok x)

theorem few (floor : ordinary17) (C : Circuit) (fan : FanInTwo C) (small : C.size ≤ 17)
    (hf : C.gates.countP touch ≤ 1) (ok : spec C) : False := by
  have ok' : spec (fixed C) := fun x => (fixed_eval C fan x).trans (ok x)
  rcases no_pins C hf with hh|hh
  · exact no0_absurd _ ok' hh
  · exact noz_absurd floor _ (fix_fan C fan) (by rwa [fix_size]) ok' hh
end Reader7354

namespace MarkedRestriction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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

end MarkedRestriction

open MarkedRestriction PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace OneNotPin
open MarkedRestriction PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def charged (pick : ℕ → Option (ℕ × Bool)) (count : ℕ) :=
  ((List.range' 0 count).filter fun j => (pick j).isSome).length

theorem marked {n : ℕ} (C : Circuit) (v : Fin n) (b : Bool)
    (hfan : FanInTwo C) (hnon : ∃ x : Fin n → Bool, C.eval (List.ofFn (Function.update x v b)) = false)
    (pick : ℕ → Option (ℕ × Bool))
    (usable : ∀ i (hi : i < C.gates.length) w z, pick i = some (w,z) →
      w ∈ C.gates[i].inputs ∧ (C.gates[i].op = .not → C.gates[i].inputs.length = 1) ∧
      ∀ x : Fin n → Bool,
        (run (C.gates.take i) (List.ofFn (Function.update x v b))).getD w false = z) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + charged pick C.gates.length ≤ C.size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x v b)) := by
  classical
  let kill (j : ℕ) := (pick j).map fun pair =>
    markDirect (n+j) pair.1 pair.2 (C.gates.getD j ⟨.and, []⟩)
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
    cases hpick : pick i with
    | none => simp [kill,hpick]
    | some pair =>
      obtain ⟨w,z⟩ := pair
      obtain ⟨hm,hnot,hx⟩ := usable i hi w z hpick
      simp only [Nat.zero_add,kill,hpick,Option.map_some,List.getD_eq_getElem _ _ hi]
      change (match some (markDirect (n+i) w z C.gates[i]) with
          | none => True
          | some (.inl c) => (run C.gates raw).getD (raw.length+i) false = c
          | some (.inr u) => u < raw.length+i ∧
            (run C.gates raw).getD (raw.length+i) false = (run C.gates raw).getD u false)
      let pre := run (C.gates.take i) raw
      have hp : pre.length = n+i := by
        simp [pre,runLen,rl,List.length_take,Nat.min_eq_left (Nat.le_of_lt hi)]
      have he := mark_sound pre w z C.gates[i] (hx x) hm
        (hfan _ (List.getElem_mem hi)).2 (hcOp _ (List.getElem_mem hi)) hnot
      have hu := usefulAlias pre w z C.gates[i]
      rw [hp] at he hu
      have ev := runAt C.gates raw i hi
      change (run C.gates raw).getD (raw.length+i) false = appendValue pre C.gates[i] at ev
      cases hr : markDirect (n+i) w z C.gates[i] with
      | inl c =>
        rw [hr] at he
        exact ev.trans he.symm
      | inr u =>
        rw [hr] at he hu
        change u < n+i at hu
        have hw : u < raw.length+i := by omega
        refine ⟨hw,ev.trans ?_⟩
        rw [runEarlier C.gates raw i u (Nat.le_of_lt hi) hw]
        exact he.symm
  have bank (x : Fin n → Bool) :
      consistent S (C.wires (List.ofFn (Function.update x v b))) (D.wires (List.ofFn x)) := by
    have he := loopConsistent n kill 0 initB C.gates _ (List.ofFn x) hcOp (hgood x)
      (initFix_ok v b x) (by simp [initB,initFix,run]) (by simp) (by simp [initB,initFix])
    change consistent S (run C.gates (List.ofFn (Function.update x v b))) (run S.gates (List.ofFn x))
    simpa only [List.take_of_length_le (by simp : (List.ofFn x).length ≤ n)] using he
  have hsz : D.size + charged pick C.gates.length ≤ C.size := by
    change S.gates.length + charged pick C.gates.length ≤ C.gates.length
    have eq : charged pick C.gates.length = killedCount kill 0 C.gates.length := by
      simp [charged,killedCount,kill]
    rw [eq]
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

end OneNotPin

namespace Reader7354
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open MarkedRestriction (run run_pres)

def prune (g : Gate) : Gate := ⟨g.op,pins g⟩
def cleaned (C : Circuit) : Circuit := ⟨C.gates.map prune,C.output⟩

private theorem prune_run (gs : List Gate) (xs : List Bool) :
    run (gs.map prune) xs = run gs xs := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    change run (gs.map prune) _ = run gs _
    rw [ih]
    rcases g with ⟨op,args⟩
    cases op <;> try rfl
    cases args <;> rfl

theorem clean_eq (C : Circuit) (xs : List Bool) : (cleaned C).eval xs = C.eval xs := by
  change (run (C.gates.map prune) xs).getD C.output false = (run C.gates xs).getD C.output false
  rw [prune_run]

theorem clean_fan (C : Circuit) (h : FanInTwo C) : FanInTwo (cleaned C) := by
  intro g hg
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hg
  refine ⟨(h q hq).1,?_⟩
  change (pins q).length ≤ 2
  have bound := (h q hq).2
  cases he : q.op <;> simp [pins,he] <;> omega

def chosen (gs : List Gate) (i : ℕ) : Option (ℕ × Bool) :=
  if touch (gs.getD i ⟨.and,[]⟩) then some (0,false) else none

private theorem count_chosen (gs : List Gate) :
    OneNotPin.charged (chosen gs) gs.length = gs.countP touch := by
  let ids := List.range' 0 gs.length
  let get := fun i => gs.getD i ⟨.and,[]⟩
  have eq : ids.map get = gs := by
    apply List.ext_getElem
    · simp [ids]
    · intro i h1 h2
      simp [ids,get,List.getElem?_eq_getElem h2]
  change (ids.filter fun j => (chosen gs j).isSome).length = _
  rw [← List.countP_eq_length_filter]
  conv_rhs => rw [← eq, List.countP_map]
  apply congrArg (fun f => ids.countP f)
  funext i
  simp only [chosen,Function.comp_apply,get]
  split <;> simp_all

private theorem mapped_reader (g : Gate) (hit : touch g = true) :
    0 ∈ (prune (down g)).inputs ∧
    ((prune (down g)).op = .not → (prune (down g)).inputs.length = 1) := by
  have eq : (prune (down g)).inputs = (pins g).map collapse := by
    rcases g with ⟨op,ins⟩
    cases op <;> cases ins <;> rfl
  rw [eq]
  obtain ⟨j,hj,hv⟩ := List.any_eq_true.mp hit
  have hv' : j=0 ∨ j=10 := by simpa using hv
  refine ⟨List.mem_map.mpr ⟨j,hj,(collapse_zero_iff j).2 hv'⟩,?_⟩
  intro hn
  change g.op = .not at hn
  have sh : (pins g).length ≤ 1 := by simp [pins, hn]
  have pos := List.length_pos_of_mem hj
  simp only [List.length_map]
  omega

theorem many (floor : pinFloor) (C : Circuit) (fan : FanInTwo C) (size : C.size ≤ 17)
    (hm : 2 ≤ C.gates.countP touch) (h : spec C) : False := by
  let T := cleaned (squeeze C)
  have len : T.gates.length = C.gates.length := by simp [T,cleaned,squeeze]
  have equal (x : Fin 10 → Bool) (hx : x 0 = false) :
      T.eval (List.ofFn x) = Peter17.target x := by
    rw [show T.eval (List.ofFn x) = (squeeze C).eval (List.ofFn x) from clean_eq _ _,squeeze_eval]
    simpa [hx] using h x
  have van : ∃ x : Fin 10 → Bool, T.eval (List.ofFn (Function.update x 0 false)) = false := by
    use fun _ => false
    have eq : Function.update (fun _ : Fin 10 => false) 0 false = (fun _ => false) := by
      funext i; by_cases h : i = 0 <;> simp [Function.update,h]
    rw [eq,equal _ rfl]
    rfl
  let pick := chosen C.gates
  have good : ∀ i (hi : i < T.gates.length) w z, pick i = some (w,z) →
      w ∈ T.gates[i].inputs ∧ (T.gates[i].op = .not → T.gates[i].inputs.length = 1) ∧
      ∀ x : Fin 10 → Bool, (run (T.gates.take i) (List.ofFn (Function.update x 0 false))).getD w false = z := by
    intro i hi w z hp
    have ii : i < C.gates.length := len ▸ hi
    simp only [pick,chosen,List.getD_eq_getElem _ _ ii] at hp
    split at hp
    next hit =>
      cases hp
      have eq : T.gates[i] = prune (down C.gates[i]) := by
        simp [T,cleaned,squeeze]
      rw [eq]
      obtain ⟨mem,unary⟩ := mapped_reader _ hit
      refine ⟨mem,unary,?_⟩
      intro x
      rw [run_pres _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
      simp
    next => contradiction
  obtain ⟨D,df,ds,de⟩ := OneNotPin.marked T (0 : Fin 10) false
    (clean_fan _ (squeeze_fan C fan)) van pick good
  have cost : OneNotPin.charged pick T.gates.length = C.gates.countP touch := by
    rw [len];exact count_chosen C.gates
  rw [cost] at ds
  have ts : T.size = C.size := len
  obtain ⟨x,hx,wrong⟩ := floor D df (by omega)
  have eq : Function.update x 0 false = x := by rw [←hx,Function.update_eq_self]
  exact wrong ((de x).trans (by rw [eq];exact equal x hx))

end Reader7354

namespace Peter17
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem signed17With
    (minor : ∀ (E : Circuit) (u : Nat) (b : Bool), FanInTwo E → E.size ≤ 15 →
      ∃ x : Fin 10 → Bool, x 9=false ∧ signed b ((E.wires (List.ofFn x)).getD u false) ≠ target x)
    (C : Circuit) (u : Nat) (b : Bool) (fan : FanInTwo C) (small : C.size ≤ 17) :
    ∃ x : Fin 10 → Bool, signed b ((C.wires (List.ofFn x)).getD u false) ≠ target x := by
  by_contra! agrees
  obtain ⟨F, hF⟩ : ∃ F : (Fin 10 → Bool) → Bool, F = fun x => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5 := ⟨_, rfl⟩
  obtain ⟨perm, hperm⟩ : ∃ perm : Fin 10 → Fin 10 → Fin 10, perm = ![![9, 6, 8, 5, 7, 4, 1, 3, 0, 2], ![6, 9, 7, 5, 8, 1, 4, 2, 0, 3], ![5, 7, 9, 6, 8, 0, 2, 4, 1, 3], ![5, 8, 6, 9, 7, 0, 3, 1, 4, 2], ![6, 8, 5, 7, 9, 1, 3, 0, 2, 4], ![4, 0, 1, 2, 3, 9, 5, 6, 7, 8], ![0, 4, 3, 2, 1, 5, 9, 8, 7, 6], ![1, 0, 4, 3, 2, 6, 5, 9, 8, 7], ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]] := ⟨_, rfl⟩
  let step : ∀ (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate), List Bool := fun (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) =>
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (l : List Bool), List Bool := fun (gs : List PEqualNP.CircuitLowerBounds.Gate) (l : List Bool) => gs.foldl step l
  have run_cons : ∀ (g : PEqualNP.CircuitLowerBounds.Gate) (gs : List PEqualNP.CircuitLowerBounds.Gate) (l : List Bool), run (g :: gs) l = run gs (step l g) := fun g gs l => rfl
  have run_append : ∀ (gs hs : List PEqualNP.CircuitLowerBounds.Gate) (l : List Bool), run (gs ++ hs) l = run hs (run gs l) := by
    intro gs hs l
    simp [run, List.foldl_append]
  have run_length : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate), ∀ l : List Bool, (run gs l).length = l.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro l; simp [run]
    | cons g gs ih =>
      intro l
      rw [run_cons, ih]
      simp [step]
      omega
  have run_getD_lt : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate), ∀ (l : List Bool) (i : ℕ), i < l.length → (run gs l).getD i false = l.getD i false := by
    intro gs
    induction gs with
    | nil => intro l i _; rfl
    | cons g gs ih =>
      intro l i h
      rw [run_cons, ih _ _ (by simp [step]; omega)]
      simp only [step]
      rw [List.getD_append _ _ _ _ h]
  have run_getD_ge : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (l : List Bool) (i : ℕ) (h : l.length + gs.length ≤ i), (run gs l).getD i false = false := fun gs l i h =>
      List.getD_eq_default _ _ (by rw [run_length]; exact h)
  have prefix_getD : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (l : List Bool) (p : ℕ) (hp : p ≤ gs.length) (i : ℕ), (run (gs.take p) l).getD i false = if i < l.length + p then (run gs l).getD i false else false := by
    intro gs l p hp i
    have hs : run gs l = run (gs.drop p) (run (gs.take p) l) := by
      rw [← run_append, List.take_append_drop]
    have hl : (run (gs.take p) l).length = l.length + p := by
      rw [run_length]; simp; omega
    split_ifs with h
    · rw [hs, run_getD_lt (gs.drop p) _ _ (by omega)]
    · exact List.getD_eq_default _ _ (by omega)
  have gate_val : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (l : List Bool) (p : ℕ) (hp : p < gs.length), (run gs l).getD (l.length + p) false = gs[p].op.eval (gs[p].inputs.map fun i => (run (gs.take p) l).getD i false) := by
    intro gs l p hp
    have hs : run gs l = run (gs.drop (p + 1)) (step (run (gs.take p) l) gs[p]) := by
      conv_lhs => rw [← List.take_append_drop p gs, List.drop_eq_getElem_cons hp]
      rw [run_append, run_cons]
    have hl : (run (gs.take p) l).length = l.length + p := by
      rw [run_length]; simp; omega
    rw [hs, run_getD_lt _ _ _ (by simp [step]; omega)]
    simp only [step]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    have : l.length + p - (run (gs.take p) l).length = 0 := by omega
    rw [this]
    rfl
  let effIns : ∀ (g : PEqualNP.CircuitLowerBounds.Gate), List ℕ := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
      PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => List ℕ) g.op g.inputs g.inputs (g.inputs.take 1)
        (fun _ => g.inputs) g.inputs
  have ev_and : ∀ (l : List Bool), PEqualNP.CircuitLowerBounds.GateOp.and.eval l = l.all id := fun l => rfl
  have ev_or : ∀ (l : List Bool), PEqualNP.CircuitLowerBounds.GateOp.or.eval l = l.any id := fun l => rfl
  have ev_not : ∀ (l : List Bool), PEqualNP.CircuitLowerBounds.GateOp.not.eval l = !(l.headD false) := fun l => rfl
  have eval_congr : ∀ (g : PEqualNP.CircuitLowerBounds.Gate) (f f' : ℕ → Bool) (ρ : ℕ → ℕ) (h : ∀ i ∈ effIns g, f i = f' (ρ i)), g.op.eval (g.inputs.map f) = g.op.eval ((g.inputs.map ρ).map f') := by
    intro g f f' ρ h
    rcases g with ⟨op, ins⟩
    cases op with
    | not =>
      cases ins with
      | nil => rfl
      | cons a rest =>
        have ha : f a = f' (ρ a) := h a (by simp [effIns])
        simp [ev_not, ha]
    | and =>
      have : ins.map f = (ins.map ρ).map f' := by
        rw [List.map_map]; apply List.map_congr_left; intro i hi; exact h i (by simpa [effIns] using hi)
      rw [this]
    | or =>
      have : ins.map f = (ins.map ρ).map f' := by
        rw [List.map_map]; apply List.map_congr_left; intro i hi; exact h i (by simpa [effIns] using hi)
      rw [this]
    | mod m =>
      have : ins.map f = (ins.map ρ).map f' := by
        rw [List.map_map]; apply List.map_congr_left; intro i hi; exact h i (by simpa [effIns] using hi)
      rw [this]
    | maj =>
      have : ins.map f = (ins.map ρ).map f' := by
        rw [List.map_map]; apply List.map_congr_left; intro i hi; exact h i (by simpa [effIns] using hi)
      rw [this]
  have agree : ∀ (B : ℕ → Prop) (gs : List PEqualNP.CircuitLowerBounds.Gate), ∀ (l l' : List Bool), l.length = l'.length → (∀ i, ¬ B i → l.getD i false = l'.getD i false) → (∀ p (hp : p < gs.length), ¬ B (l.length + p) → ∀ i ∈ effIns gs[p], i < l.length + p → ¬ B i) → ∀ i, ¬ B i → (run gs l).getD i false = (run gs l').getD i false := by
    intro B gs
    induction gs with
    | nil => intro l l' _ h0 _ i hi; exact h0 i hi
    | cons g gs ih =>
      intro l l' hlen h0 hg
      rw [run_cons, run_cons]
      apply ih
      · simp [step, hlen]
      · intro i hi
        simp only [step]
        by_cases hil : i < l.length
        · rw [List.getD_append _ _ _ _ hil, List.getD_append _ _ _ _ (by omega)]
          exact h0 i hi
        · by_cases hie : i = l.length
          · subst hie
            rw [List.getD_append_right _ _ _ _ le_rfl, List.getD_append_right _ _ _ _ (by omega)]
            simp only [Nat.sub_self, hlen]
            simp only [List.getD_cons_zero]
            have := eval_congr g (fun i => l.getD i false) (fun i => l'.getD i false) id (by
              intro j hj
              by_cases hjl : j < l.length
              · have := hg 0 (by simp) (by simpa [hlen] using hi) j (by simpa using hj) (by omega)
                exact h0 j this
              · simp only [id]
                rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)])
            simpa using this
          · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      · intro p hp hB i hi hil
        have := hg (p + 1) (by simp; omega) (by simpa [step, Nat.add_assoc, Nat.add_comm 1 p] using hB) i
          (by simpa using hi) (by simp [step] at hil; omega)
        exact this
  let redir : ∀ (k r i : ℕ), ℕ := fun (k r i : ℕ) => if i = k then r else if k < i then i - 1 else i
  have redir_eq : ∀ (k r : ℕ), redir k r k = r := by
    intro k r
    simp [redir]
  have redir_gt : ∀ (k r i : ℕ) (h : k < i), redir k r i = i - 1 := by
    intro k r i h
    simp [redir, h, Nat.ne_of_gt h]
  have redir_lt : ∀ (k r i : ℕ) (h : i < k), redir k r i = i := by
    intro k r i h
    simp [redir, Nat.ne_of_lt h, Nat.not_lt.mpr h.le]
  let mapG : ∀ (k r : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), PEqualNP.CircuitLowerBounds.Gate := fun (k r : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) => ⟨g.op, g.inputs.map (redir k r)⟩
  let FT : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate), Prop := fun (gs : List PEqualNP.CircuitLowerBounds.Gate) =>
      ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2
  let reads : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (p w : ℕ), Prop := fun (gs : List PEqualNP.CircuitLowerBounds.Gate) (p w : ℕ) => ∃ hp : p < gs.length, w ∈ effIns gs[p] ∧ w < 10 + p
  let erased : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (m r : ℕ), List PEqualNP.CircuitLowerBounds.Gate := fun (gs : List PEqualNP.CircuitLowerBounds.Gate) (m r : ℕ) =>
      gs.take m ++ (gs.drop (m + 1)).map (mapG (10 + m) r)
  let Comp : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : ℕ) (b : Bool) (S : (Fin 10 → Bool) → Prop), Prop := fun (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : ℕ) (b : Bool) (S : (Fin 10 → Bool) → Prop) =>
      ∀ x, S x → (if b = true then !((run gs (List.ofFn x)).getD u false)
        else (run gs (List.ofFn x)).getD u false) = F x
  let Rem : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : ℕ) (S : (Fin 10 → Bool) → Prop) (m r : ℕ), Prop := fun (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : ℕ) (S : (Fin 10 → Bool) → Prop) (m r : ℕ) =>
      m < gs.length ∧ r < 10 + m ∧
        ((∀ x, S x → (run gs (List.ofFn x)).getD r false = (run gs (List.ofFn x)).getD (10 + m) false) ∨
          ((∀ p, ¬ reads gs p (10 + m)) ∧ u ≠ 10 + m))
  have erase_inv : ∀ (k r : ℕ) (A : List Bool) (hA : A.length = k) (val : Bool), ∀ (post : List PEqualNP.CircuitLowerBounds.Gate) (T : List Bool), (∀ g ∈ post, k ∈ effIns g → (r < k ∧ A.getD r false = val) ∨ (k + T.length + post.length ≤ r ∧ val = false)) → run (post.map (mapG k r)) (A ++ T) = (run post (A ++ val :: T)).eraseIdx k := by
    intro k r A hA val
    intro post
    induction post with
    | nil =>
      intro T _
      simp [run, hA, List.eraseIdx_append_of_length_le]
    | cons g post ih =>
      intro T hpost
      have hval : g.op.eval (g.inputs.map fun i => (A ++ val :: T).getD i false) =
          (mapG k r g).op.eval ((mapG k r g).inputs.map fun i => (A ++ T).getD i false) := by
        apply eval_congr g _ _ (redir k r)
        intro i hi
        dsimp only [redir]
        by_cases hik : i = k
        · rw [if_pos hik]
          have hcase := hpost g (List.mem_cons_self) (hik ▸ hi)
          have hL : (A ++ val :: T).getD i false = val := by
            rw [List.getD_append_right _ _ _ _ (by omega)]
            have : i - A.length = 0 := by omega
            rw [this]; rfl
          rw [hL]
          rcases hcase with ⟨hrk, hrv⟩ | ⟨hrbig, hvf⟩
          · rw [List.getD_append _ _ _ _ (by omega), hrv]
          · rw [List.getD_eq_default _ _ (by simp; omega), hvf]
        · by_cases hlt : k < i
          · rw [if_neg hik, if_pos hlt]
            rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
            obtain ⟨j, rfl⟩ : ∃ j, i = k + 1 + j := ⟨i - k - 1, by omega⟩
            have e1 : k + 1 + j - A.length = j + 1 := by omega
            have e2 : k + 1 + j - 1 - A.length = j := by omega
            rw [e1, e2]
            simp
          · rw [if_neg hik, if_neg hlt]
            rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      have hrest := ih (T ++ [g.op.eval (g.inputs.map fun i => (A ++ val :: T).getD i false)]) (by
        intro g' hg' hk'
        rcases hpost g' (List.mem_cons_of_mem _ hg') hk' with h | ⟨h1, h2⟩
        · exact Or.inl h
        · right; refine ⟨?_, h2⟩; simp at h1 ⊢; omega)
      rw [List.map_cons, run_cons, run_cons]
      simp only [step] at hrest ⊢
      rw [← hval]
      simpa [List.append_assoc] using hrest
  have erase_main : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (m r : ℕ) (hm : m < gs.length) (hr : r < 10 + m) (l : List Bool) (hl : l.length = 10) (hcond : (run gs l).getD r false = (run gs l).getD (10 + m) false ∨ ∀ p, ¬ reads gs p (10 + m)), run (erased gs m r) l = (run gs l).eraseIdx (10 + m) := by
    intro gs m r hm hr l hl hcond
    have hA : (run (gs.take m) l).length = 10 + m := by
      rw [run_length]; simp; omega
    have hs : run gs l = run (gs.drop (m + 1)) (run (gs.take m) l ++
        [gs[m].op.eval (gs[m].inputs.map fun i => (run (gs.take m) l).getD i false)]) := by
      conv_lhs => rw [← List.take_append_drop m gs, List.drop_eq_getElem_cons hm]
      rw [run_append, run_cons]
      try rfl
    have hnew : run (erased gs m r) l = run ((gs.drop (m + 1)).map (mapG (10 + m) r)) (run (gs.take m) l) := by
      simp only [erased]
      rw [run_append]
    have key := erase_inv (10 + m) r (run (gs.take m) l) hA
      (gs[m].op.eval (gs[m].inputs.map fun i => (run (gs.take m) l).getD i false)) (gs.drop (m + 1)) [] (by
        intro g hg hk
        rcases hcond with hc | hd
        · left
          refine ⟨hr, ?_⟩
          rw [prefix_getD gs l m hm.le r, if_pos (by omega), hc]
          have := gate_val gs l m hm
          rw [hl] at this
          exact this
        · exfalso
          obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
          rw [List.getElem_drop] at hk
          exact hd (m + 1 + j) ⟨by simp at hj; omega, hk, by omega⟩)
    rw [hnew, hs]
    simpa using key
  have eraseIdx_getD : ∀ (L : List Bool) (k j : ℕ), (L.eraseIdx k).getD j false = L.getD (if j < k then j else j + 1) false := by
    intro L k j
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx]
    split_ifs <;> rfl
  have effIns_mapG : ∀ (k r : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), effIns (mapG k r g) = (effIns g).map (redir k r) := by
    intro k r g
    rcases g with ⟨op, ins⟩
    cases op <;> simp [effIns, mapG, List.map_take]
  have erase_ok : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : ℕ) (b : Bool) (S : (Fin 10 → Bool) → Prop) (m r : ℕ) (hFT : FT gs) (hC : Comp gs u b S) (hR : Rem gs u S m r), FT (erased gs m r) ∧ (erased gs m r).length + 1 = gs.length ∧ Comp (erased gs m r) (redir (10 + m) r u) b S ∧ (∀ p w, p ≠ m → w < 10 + m → reads gs p w → reads (erased gs m r) (if p < m then p else p - 1) w) := by
    intro gs u b S m r hFT hC hR
    obtain ⟨hm, hr, hcase⟩ := hR
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [erased, List.mem_append, List.mem_map] at hg
      rcases hg with hg | ⟨g0, hg0, rfl⟩
      · exact hFT g (List.mem_of_mem_take hg)
      · have := hFT g0 (List.mem_of_mem_drop hg0)
        simpa [mapG] using this
    · simp [erased]; omega
    · intro x hx
      have hmain := erase_main gs m r hm hr (List.ofFn x) (by simp) (by
        rcases hcase with hc | ⟨hd, _⟩
        · exact Or.inl (hc x hx)
        · exact Or.inr hd)
      rw [hmain, eraseIdx_getD]
      have hval : (run gs (List.ofFn x)).getD (if redir (10 + m) r u < 10 + m then redir (10 + m) r u
          else redir (10 + m) r u + 1) false = (run gs (List.ofFn x)).getD u false := by
        by_cases hu : u = 10 + m
        · rw [hu, redir_eq, if_pos hr]
          rcases hcase with hc | ⟨_, hne⟩
          · rw [hc x hx]
          · exact absurd hu hne
        · by_cases hlt : 10 + m < u
          · rw [redir_gt _ _ _ hlt, if_neg (by omega)]
            congr 1; omega
          · rw [redir_lt _ _ _ (by omega), if_pos (by omega)]
      rw [hval]
      exact hC x hx
    · intro p w hpm hw hrd
      obtain ⟨hp, hwe, hwl⟩ := hrd
      by_cases hlt : p < m
      · rw [if_pos hlt]
        refine ⟨by simp [erased]; omega, ?_, hwl⟩
        have : (erased gs m r)[p]'(by simp [erased]; omega) = gs[p] := by
          simp only [erased]
          rw [List.getElem_append_left (by simp; omega)]
          simp
        rw [this]; exact hwe
      · rw [if_neg hlt]
        have hpm' : m < p := by omega
        refine ⟨by simp [erased]; omega, ?_, by omega⟩
        have : (erased gs m r)[p - 1]'(by simp [erased]; omega) = mapG (10 + m) r gs[p] := by
          simp only [erased]
          rw [List.getElem_append_right (by simp; omega)]
          simp only [List.getElem_map, List.getElem_drop]
          congr 2
          simp; omega
        rw [this, effIns_mapG]
        have hw' : redir (10 + m) r w = w := by
          exact redir_lt _ _ _ hw
        rw [← hw']
        exact List.mem_map_of_mem hwe
  have gate_shape : ∀ (op : PEqualNP.CircuitLowerBounds.GateOp) (ins : List ℕ) (hop : op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp)) (hlen : ins.length ≤ 2) (w : ℕ) (hwe : w ∈ effIns ⟨op, ins⟩), (∃ φ : Bool → Bool, ∀ f : ℕ → Bool, op.eval (ins.map f) = φ (f w)) ∨ (∃ y, y ≠ w ∧ (ins = [w, y] ∨ ins = [y, w]) ∧ ((op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ f : ℕ → Bool, op.eval (ins.map f) = (f w || f y)) ∨ (op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∀ f : ℕ → Bool, op.eval (ins.map f) = (f w && f y)))) := by
    intro op ins hop hlen w hwe
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩
      · simp [effIns] at hwe
      · simp [effIns] at hwe; subst hwe
        left; exact ⟨id, fun f => by simp [ev_and, ev_or, ev_not]⟩
      · simp [effIns] at hwe
        by_cases hab : a = b
        · subst hab
          rcases hwe with rfl | rfl <;> (left; exact ⟨id, fun f => by simp [ev_and, ev_or, ev_not]⟩)
        · rcases hwe with rfl | rfl
          · right; exact ⟨b, Ne.symm hab, Or.inl rfl, Or.inr ⟨rfl, fun f => by simp [ev_and, ev_or, ev_not]⟩⟩
          · right; refine ⟨a, hab, Or.inr rfl, Or.inr ⟨rfl, fun f => ?_⟩⟩
            simp [ev_and, Bool.and_comm]
      · simp at hlen
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩
      · simp [effIns] at hwe
      · simp [effIns] at hwe; subst hwe
        left; exact ⟨id, fun f => by simp [ev_and, ev_or, ev_not]⟩
      · simp [effIns] at hwe
        by_cases hab : a = b
        · subst hab
          rcases hwe with rfl | rfl <;> (left; exact ⟨id, fun f => by simp [ev_and, ev_or, ev_not]⟩)
        · rcases hwe with rfl | rfl
          · right; exact ⟨b, Ne.symm hab, Or.inl rfl, Or.inl ⟨rfl, fun f => by simp [ev_and, ev_or, ev_not]⟩⟩
          · right; refine ⟨a, hab, Or.inr rfl, Or.inl ⟨rfl, fun f => ?_⟩⟩
            simp [ev_or, Bool.or_comm]
      · simp at hlen
    · rcases ins with _ | ⟨a, rest⟩
      · simp [effIns] at hwe
      · simp [effIns] at hwe; subst hwe
        left; exact ⟨fun t => !t, fun f => by simp [ev_and, ev_or, ev_not]⟩
  have step_lemma : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (hFT : FT gs) (S : (Fin 10 → Bool) → Prop) (w : ℕ) (c : Bool) (hw : ∀ x, S x → (run gs (List.ofFn x)).getD w false = c) (p : ℕ) (hp : reads gs p w), (∃ c', ∀ x, S x → (run gs (List.ofFn x)).getD (10 + p) false = c') ∨ (∃ (hp' : p < gs.length) (y : ℕ), y < 10 + p ∧ y ≠ w ∧ (gs[p].inputs = [w, y] ∨ gs[p].inputs = [y, w]) ∧ ((gs[p].op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ c = false) ∨ (gs[p].op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ c = true)) ∧ ∀ x, S x → (run gs (List.ofFn x)).getD (10 + p) false = (run gs (List.ofFn x)).getD y false) := by
    intro gs hFT S w c hw p hp
    obtain ⟨hp', hwe, hwl⟩ := hp
    have hval : ∀ x : Fin 10 → Bool, (run gs (List.ofFn x)).getD (10 + p) false =
        gs[p].op.eval (gs[p].inputs.map fun i =>
          if i < 10 + p then (run gs (List.ofFn x)).getD i false else false) := by
      intro x
      have h1 := gate_val gs (List.ofFn x) p hp'
      simp only [List.length_ofFn] at h1
      rw [h1]
      congr 1
      apply List.map_congr_left
      intro i _
      rw [prefix_getD gs (List.ofFn x) p hp'.le i]
      simp
    obtain ⟨hop, hlen⟩ := hFT gs[p] (List.getElem_mem hp')
    rcases gate_shape gs[p].op gs[p].inputs hop hlen w hwe with ⟨φ, hφ⟩ | ⟨y, hyw, hins, hcase⟩
    · left
      refine ⟨φ c, fun x hx => ?_⟩
      rw [hval x, hφ, if_pos hwl, hw x hx]
    · rcases hcase with ⟨hor, hf⟩ | ⟨hand, hf⟩
      · cases c
        · by_cases hy : y < 10 + p
          · right
            refine ⟨hp', y, hy, hyw, hins, Or.inl ⟨hor, rfl⟩, fun x hx => ?_⟩
            rw [hval x, hf, if_pos hwl, hw x hx, if_pos hy]
            simp
          · left
            refine ⟨false, fun x hx => ?_⟩
            rw [hval x, hf, if_pos hwl, hw x hx, if_neg hy]
            simp
        · left
          refine ⟨true, fun x hx => ?_⟩
          rw [hval x, hf, if_pos hwl, hw x hx]
          simp
      · cases c
        · left
          refine ⟨false, fun x hx => ?_⟩
          rw [hval x, hf, if_pos hwl, hw x hx]
          simp
        · by_cases hy : y < 10 + p
          · right
            refine ⟨hp', y, hy, hyw, hins, Or.inr ⟨hand, rfl⟩, fun x hx => ?_⟩
            rw [hval x, hf, if_pos hwl, hw x hx, if_pos hy]
            simp
          · left
            refine ⟨false, fun x hx => ?_⟩
            rw [hval x, hf, if_pos hwl, hw x hx, if_neg hy]
            simp
  have chain : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (hFT : FT gs) (u : ℕ) (S : (Fin 10 → Bool) → Prop) (hnc : ∃ x x', S x ∧ S x' ∧
      (run gs (List.ofFn x)).getD u false ≠ (run gs (List.ofFn x')).getD u false), ∀ k q c, gs.length - q = k → q < gs.length → (∀ x, S x → (run gs (List.ofFn x)).getD (10 + q) false = c) → ∃ m r, Rem gs u S m r ∧ q ≤ m ∧ (m = q → (∀ p, ¬ reads gs p (10 + q)) ∧ u ≠ 10 + q) := by
    intro gs hFT u S hnc
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro q c hk hq hc
    have hu : u ≠ 10 + q := by
      rintro rfl
      obtain ⟨x, x', hx, hx', hne⟩ := hnc
      exact hne (by rw [hc x hx, hc x' hx'])
    by_cases hrd : ∃ p, reads gs p (10 + q)
    · obtain ⟨p, hp⟩ := hrd
      have hpq : q < p := by obtain ⟨_, _, h⟩ := hp; omega
      rcases step_lemma gs hFT S (10 + q) c hc p hp with ⟨c', hc'⟩ | ⟨hp', y, hy, _, _, _, hcopy⟩
      · obtain ⟨m, r, hR, hpm, _⟩ := ih (gs.length - p) (by omega) p c' rfl hp.1 hc'
        exact ⟨m, r, hR, by omega, fun h => by omega⟩
      · exact ⟨p, y, ⟨hp', hy, Or.inl (fun x hx => (hcopy x hx).symm)⟩, by omega, fun h => by omega⟩
    · push Not at hrd
      exact ⟨q, 0, ⟨hq, by omega, Or.inr ⟨hrd, hu⟩⟩, le_rfl, fun _ => ⟨hrd, hu⟩⟩
  have ofFn_getD : ∀ (x : Fin 10 → Bool) (v : Fin 10), (List.ofFn x).getD v false = x v := by
    intro x v
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [v.isLt]
  have nonconst_of_comp : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : ℕ) (b : Bool) (S : (Fin 10 → Bool) → Prop) (hC : Comp gs u b S) (h : ∃ x x', S x ∧ S x' ∧ F x ≠ F x'), ∃ x x', S x ∧ S x' ∧ (run gs (List.ofFn x)).getD u false ≠ (run gs (List.ofFn x')).getD u false := by
    intro gs u b S hC h
    obtain ⟨x, x', hx, hx', hne⟩ := h
    refine ⟨x, x', hx, hx', fun heq => hne ?_⟩
    rw [← hC x hx, ← hC x' hx', heq]
  have PF_edge : ∀ v : Fin 10, ∃ a b : Fin 10, a ≠ v ∧ b ≠ v ∧ F (fun i => decide (i = a) || decide (i = b)) = true := by
    subst hF; decide
  have PF_zero : F (fun _ => false) = false := by
    subst hF; decide
  have PF_noncon : ∀ (v : Fin 10), ∃ x x' : Fin 10 → Bool, x v = false ∧ x' v = false ∧ F x ≠ F x' := by
    intro v
    obtain ⟨a, b, ha, hb, h⟩ := PF_edge v
    refine ⟨fun _ => false, fun i => decide (i = a) || decide (i = b), rfl, ?_, ?_⟩
    · simp [Ne.symm ha, Ne.symm hb]
    · rw [h, PF_zero]; decide
  have single_rem : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (hFT : FT gs) (u : ℕ) (b : Bool) (v : Fin 10) (hC : Comp gs u b (fun x => x v = false)) (p : ℕ) (hp : reads gs p v), ∃ gs' u', FT gs' ∧ gs'.length + 1 = gs.length ∧ Comp gs' u' b (fun x => x v = false) := by
    intro gs hFT u b v hC p hp
    have hnc := nonconst_of_comp gs u b _ hC (PF_noncon v)
    have hwv : ∀ x : Fin 10 → Bool, x v = false → (run gs (List.ofFn x)).getD v false = false := by
      intro x hx
      rw [run_getD_lt _ _ _ (by simp), ofFn_getD, hx]
    obtain ⟨m, r, hR⟩ : ∃ m r, Rem gs u (fun x => x v = false) m r := by
      rcases step_lemma gs hFT _ v false hwv p hp with ⟨c', hc'⟩ | ⟨hp', y, hy, _, _, _, hcopy⟩
      · obtain ⟨m, r, hR, _⟩ := chain gs hFT u _ hnc _ p c' rfl hp.1 hc'
        exact ⟨m, r, hR⟩
      · exact ⟨p, y, hp', hy, Or.inl fun x hx => (hcopy x hx).symm⟩
    obtain ⟨h1, h2, h3, _⟩ := erase_ok gs u b _ m r hFT hC hR
    exact ⟨_, _, h1, h2, h3⟩
  have ofFn_getD' : ∀ (x : Fin 10 → Bool) (i : ℕ), (List.ofFn x).getD i false = if h : i < 10 then x ⟨i, h⟩ else false := by
    intro x i
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    split_ifs <;> simp
  have agree_x : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (B : ℕ → Prop) (x x' : Fin 10 → Bool) (hx : ∀ i : Fin 10, ¬ B i → x i = x' i) (hg : ∀ p i, ¬ B (10 + p) → reads gs p i → ¬ B i) (u : ℕ) (hu : ¬ B u), (run gs (List.ofFn x)).getD u false = (run gs (List.ofFn x')).getD u false := by
    intro gs B x x' hx hg u hu
    apply agree B gs (List.ofFn x) (List.ofFn x') (by simp)
    · intro i hi
      rw [ofFn_getD', ofFn_getD']
      split_ifs with h
      · exact hx ⟨i, h⟩ hi
      · rfl
    · intro p hp hB i hi hil
      simp only [List.length_ofFn] at hB hil
      exact hg p i hB ⟨hp, hi, hil⟩
    · exact hu
  have PF_dep' : ∀ v : Fin 10, ∃ a : Fin 10, a ≠ v ∧ F (fun i => decide (i = v) || decide (i = a)) ≠ F (fun i => decide (i = a)) := by
    subst hF; decide
  have PF_dep : ∀ (v : Fin 10), ∃ x x' : Fin 10 → Bool, (∀ i, i ≠ v → x i = x' i) ∧ F x ≠ F x' := by
    intro v
    obtain ⟨a, _, h⟩ := PF_dep' v
    refine ⟨_, _, fun i hi => ?_, h⟩
    simp [hi]
  have PF_single : ∀ i : Fin 10, F (fun j => decide (j = i)) = false := by
    subst hF; decide
  have PF_or' : ∀ v w : Fin 10, v ≠ w → ∃ a : Fin 10, F (fun i => decide (i = v) || decide (i = a)) ≠ F (fun i => decide (i = w) || decide (i = a)) := by
    subst hF; decide
  have out_ge : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : ℕ) (b : Bool) (hC : Comp gs u b (fun _ => True)), 10 ≤ u := by
    intro gs u b hC
    by_contra h
    push Not at h
    have hv : ∀ x : Fin 10 → Bool, (run gs (List.ofFn x)).getD u false = x ⟨u, h⟩ := by
      intro x
      rw [run_getD_lt _ _ _ (by simpa using h), ofFn_getD']
      simp [h]
    cases b
    · have := hC (fun j => decide (j = ⟨u, h⟩)) trivial
      rw [hv, PF_single] at this
      simp at this
    · have := hC (fun _ => false) trivial
      rw [hv, PF_zero] at this
      simp at this
  have has_reader : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : ℕ) (b : Bool) (hC : Comp gs u b (fun _ => True)) (v : Fin 10), ∃ p, reads gs p v := by
    intro gs u b hC v
    by_contra h
    push Not at h
    have hu := out_ge gs u b hC
    obtain ⟨x, x', hxx, hne⟩ := PF_dep v
    apply hne
    rw [← hC x trivial, ← hC x' trivial]
    rw [agree_x gs (fun i => i = (v : ℕ)) x x' (fun i hi => hxx i (fun h' => hi (by rw [h'])))
      (fun p i _ hr hi => by rw [hi] at hr; exact h p hr) u (by omega)]
  have one_rem : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (hFT : FT gs) (u : ℕ) (b : Bool) (hC : Comp gs u b (fun _ => True)), ∃ gs' u', FT gs' ∧ gs'.length + 1 = gs.length ∧ Comp gs' u' b (fun x => x 9 = false) := by
    intro gs hFT u b hC
    obtain ⟨p, hp⟩ := has_reader gs u b hC 9
    exact single_rem gs hFT u b 9 (fun x _ => hC x trivial) p hp
  let bad : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (v : ℕ), Prop := fun (gs : List PEqualNP.CircuitLowerBounds.Gate) (v : ℕ) =>
      ∃ r, (∀ p, reads gs p v → p = r) ∧ ∃ hr : r < gs.length, gs[r].op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        ∃ y, y < 10 + r ∧ y ≠ v ∧ (gs[r].inputs = [v, y] ∨ gs[r].inputs = [y, v])
  have good_two : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (hFT : FT gs) (u : ℕ) (b : Bool) (hC : Comp gs u b (fun _ => True)) (v : Fin 10) (hgood : ¬ bad gs v), ∃ gs'' u'', FT gs'' ∧ gs''.length + 2 = gs.length ∧ Comp gs'' u'' b (fun x => x v = false) := by
    intro gs hFT u b hC v hgood
    have hu10 := out_ge gs u b hC
    have hCS : Comp gs u b (fun x => x v = false) := fun x _ => hC x trivial
    have hnc := nonconst_of_comp gs u b _ hCS (PF_noncon v)
    have hwv : ∀ x : Fin 10 → Bool, x v = false → (run gs (List.ofFn x)).getD v false = false := by
      intro x hx
      rw [run_getD_lt _ _ _ (by simp), ofFn_getD, hx]
    suffices H : ∃ m r p, Rem gs u (fun x => x v = false) m r ∧ p ≠ m ∧ reads gs p v by
      obtain ⟨m, r, p, hR, hpm, hp⟩ := H
      obtain ⟨h1, h2, h3, h4⟩ := erase_ok gs u b _ m r hFT hCS hR
      have hp' := h4 p v hpm (by omega) hp
      obtain ⟨gs'', u'', k1, k2, k3⟩ := single_rem _ h1 _ b v h3 _ hp'
      exact ⟨gs'', u'', k1, by omega, k3⟩
    by_cases h2 : ∃ p1 p2, p1 ≠ p2 ∧ reads gs p1 v ∧ reads gs p2 v
    · obtain ⟨p1, p2, hne, hp1, hp2⟩ := h2
      obtain ⟨m, r, hR⟩ : ∃ m r, Rem gs u (fun x => x v = false) m r := by
        rcases step_lemma gs hFT _ v false hwv p1 hp1 with ⟨c', hc'⟩ | ⟨hp', y, hy, _, _, _, hcopy⟩
        · obtain ⟨m, r, hR, _⟩ := chain gs hFT u _ hnc _ p1 c' rfl hp1.1 hc'
          exact ⟨m, r, hR⟩
        · exact ⟨p1, y, hp', hy, Or.inl fun x hx => (hcopy x hx).symm⟩
      by_cases hm : p1 = m
      · exact ⟨m, r, p2, hR, by rw [← hm]; exact Ne.symm hne, hp2⟩
      · exact ⟨m, r, p1, hR, hm, hp1⟩
    · obtain ⟨q, hq⟩ := has_reader gs u b hC v
      have huniq : ∀ p, reads gs p v → p = q := by
        intro p hp
        by_contra hne
        exact h2 ⟨p, q, hne, hp, hq⟩
      rcases step_lemma gs hFT _ v false hwv q hq with ⟨c', hc'⟩ | ⟨hq', y, hy, hyv, hins, hopc, _⟩
      · obtain ⟨m, r, hR, hqm, hdead⟩ := chain gs hFT u _ hnc _ q c' rfl hq.1 hc'
        by_cases hmq : m = q
        · exfalso
          obtain ⟨hnr, hune⟩ := hdead hmq
          obtain ⟨x, x', hxx, hne⟩ := PF_dep v
          apply hne
          rw [← hC x trivial, ← hC x' trivial]
          rw [agree_x gs (fun i => i = (v : ℕ) ∨ i = 10 + q) x x'
            (fun i hi => hxx i (fun h' => hi (Or.inl (by rw [h']))))
            (fun p i hB hr hi => by
              rcases hi with hi | hi
              · rw [hi] at hr
                have := huniq p hr
                exact hB (Or.inr (by rw [this]))
              · rw [hi] at hr
                exact hnr p hr)
            u (by
              rintro (h | h)
              · omega
              · exact hune h)]
        · exact ⟨m, r, q, hR, Ne.symm hmq, hq⟩
      · exfalso
        apply hgood
        refine ⟨q, huniq, hq', ?_, y, hy, hyv, hins⟩
        rcases hopc with ⟨h, _⟩ | ⟨_, h⟩
        · exact h
        · exact absurd h (by decide)
  have first_gate : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (hFT : FT gs) (u : ℕ) (b : Bool) (hC : Comp gs u b (fun _ => True)) (hne : 0 < gs.length) (hbad : ∀ v : Fin 10, bad gs v), ∃ c, ∀ x : Fin 10 → Bool, True → (run gs (List.ofFn x)).getD (10 + 0) false = c := by
    intro gs hFT u b hC hne hbad
    have hu10 := out_ge gs u b hC
    by_cases hrd : ∃ v : Fin 10, reads gs 0 v
    · exfalso
      obtain ⟨v, hv⟩ := hrd
      obtain ⟨r, huniq, hr, hor, y, hy, hyv, hins⟩ := hbad v
      have hr0 : r = 0 := (huniq 0 hv).symm
      subst hr0
      have hy10 : y < 10 := by omega
      have hyr : reads gs 0 y := by
        refine ⟨hr, ?_, by omega⟩
        simp only [effIns, hor]
        rcases hins with h | h <;> rw [h] <;> simp
      obtain ⟨r', huniq', -⟩ := hbad ⟨y, hy10⟩
      have hr'0 : r' = 0 := (huniq' 0 hyr).symm
      subst hr'0
      obtain ⟨a, ha⟩ := PF_or' v ⟨y, hy10⟩ (fun h => hyv (by subst h; rfl))
      set x : Fin 10 → Bool := fun i => decide (i = v) || decide (i = a) with hxdef
      set x' : Fin 10 → Bool := fun i => decide (i = (⟨y, hy10⟩ : Fin 10)) || decide (i = a) with hx'def
      have key : (run gs (List.ofFn x)).getD u false = (run gs (List.ofFn x')).getD u false := by
        obtain ⟨g0, rest, hgs⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos hne)
        subst hgs
        simp only [List.getElem_cons_zero] at hor hins
        rw [run_cons, run_cons]
        apply agree (fun i => i = (v : ℕ) ∨ i = y) rest _ _ (by simp [step])
        · intro i hi
          simp only [step]
          by_cases hil : i < 10
          · rw [List.getD_append _ _ _ _ (by simpa using hil), List.getD_append _ _ _ _ (by simpa using hil),
              ofFn_getD', ofFn_getD', dif_pos hil, dif_pos hil]
            have h1 : (⟨i, hil⟩ : Fin 10) ≠ v := fun h => hi (Or.inl (by rw [← h]))
            have h2 : (⟨i, hil⟩ : Fin 10) ≠ ⟨y, hy10⟩ := fun h => hi (Or.inr (by
              have := congrArg Fin.val h; simpa using this))
            simp [hxdef, hx'def, h1, h2]
          · by_cases hi10 : i = 10
            · subst hi10
              rw [List.getD_append_right _ _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)]
              simp only [List.length_ofFn, Nat.sub_self, List.getD_cons_zero]
              have e1 : (List.ofFn x).getD v false = true := by rw [ofFn_getD]; simp [hxdef]
              have e2 : (List.ofFn x').getD y false = true := by
                rw [ofFn_getD' x' y, dif_pos hy10]; simp [hx'def]
              rcases hins with h | h <;> rw [h, hor] <;>
                simp only [ev_or, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
                  e1, e2] <;> simp
            · rw [List.getD_eq_default _ _ (by simp; omega),
                List.getD_eq_default _ _ (by simp; omega)]
        · intro p hp hB i hi hil
          rintro (h | h)
          · have := huniq (p + 1) ⟨by simp; omega, by simpa [h] using hi, by simp [step] at hil; omega⟩
            omega
          · have := huniq' (p + 1) ⟨by simp; omega, by simpa [h] using hi, by simp [step] at hil; omega⟩
            omega
        · rintro (h | h) <;> omega
      apply ha
      rw [← hC x trivial, ← hC x' trivial, key]
    · push Not at hrd
      obtain ⟨g0, rest, hgs⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos hne)
      refine ⟨g0.op.eval ((g0.inputs.map id).map fun _ => false), fun x _ => ?_⟩
      have hv := gate_val gs (List.ofFn x) 0 hne
      simp only [List.length_ofFn, List.take_zero] at hv
      rw [hv]
      have hg0 : gs[0] = g0 := by subst hgs; rfl
      rw [hg0]
      apply eval_congr g0 _ _ id
      intro i hi
      have hi10 : ¬ i < 10 := by
        intro hi10
        apply hrd ⟨i, hi10⟩
        exact ⟨hne, by rw [hg0]; exact hi, by simpa using hi10⟩
      simp only [run]
      rw [List.foldl_nil, List.getD_eq_default _ _ (by simp; omega)]
  let rlbl : ∀ (π : Fin 10 → Fin 10) (i : ℕ), ℕ := fun (π : Fin 10 → Fin 10) (i : ℕ) => if h : i < 10 then (π ⟨i, h⟩ : ℕ) else i
  let rlblG : ∀ (π : Fin 10 → Fin 10) (g : PEqualNP.CircuitLowerBounds.Gate), PEqualNP.CircuitLowerBounds.Gate := fun (π : Fin 10 → Fin 10) (g : PEqualNP.CircuitLowerBounds.Gate) => ⟨g.op, g.inputs.map (rlbl π)⟩
  have rlbl_run : ∀ (π : Fin 10 → Fin 10) (gs : List PEqualNP.CircuitLowerBounds.Gate), ∀ (L L' : List Bool), L.length = L'.length → 10 ≤ L.length → (∀ k, L.getD (rlbl π k) false = L'.getD k false) → ∀ k, (run (gs.map (rlblG π)) L).getD (rlbl π k) false = (run gs L').getD k false := by
    intro π gs
    induction gs with
    | nil => intro L L' _ _ h k; exact h k
    | cons g gs ih =>
      intro L L' hlen h10 h
      rw [List.map_cons, run_cons, run_cons]
      apply ih
      · simp [step, hlen]
      · simp [step]; omega
      · intro k
        simp only [step]
        have hval : (rlblG π g).op.eval ((rlblG π g).inputs.map fun i => L.getD i false) =
            g.op.eval (g.inputs.map fun i => L'.getD i false) := by
          symm
          exact eval_congr g _ _ (rlbl π) (fun i _ => (h i).symm)
        rw [hval]
        by_cases hk : k < 10
        · have hr : rlbl π k = π ⟨k, hk⟩ := by simp [rlbl, hk]
          rw [hr, List.getD_append _ _ _ _ (by have := (π ⟨k, hk⟩).isLt; omega),
            List.getD_append _ _ _ _ (by omega), ← hr]
          exact h k
        · have hr : rlbl π k = k := by simp [rlbl, hk]
          rw [hr]
          by_cases hkl : k < L.length
          · rw [List.getD_append _ _ _ _ hkl, List.getD_append _ _ _ _ (by omega)]
            have := h k
            rwa [hr] at this
          · by_cases hke : k = L.length
            · subst hke
              rw [List.getD_append_right _ _ _ _ le_rfl, List.getD_append_right _ _ _ _ (by omega)]
              simp [hlen]
            · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  have perm9 : ∀ v : Fin 10, perm v v = 9 := by
    subst hperm; decide
  have PF_bits : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : Bool, ∀ v : Fin 10, F (![a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] ∘ perm v) = F ![a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] := by
    subst hF hperm; decide
  have perm_aut : ∀ (v : Fin 10) (x : Fin 10 → Bool), F (x ∘ perm v) = F x := by
    intro v x
    have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9] := by
      funext i; fin_cases i <;> rfl
    rw [hx]
    exact PF_bits _ _ _ _ _ _ _ _ _ _ v
  have rlbl_comp : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (hFT : FT gs) (u : ℕ) (b : Bool) (v : Fin 10) (hC : Comp gs u b (fun x => x v = false)), FT (gs.map (rlblG (perm v))) ∧ (gs.map (rlblG (perm v))).length = gs.length ∧ Comp (gs.map (rlblG (perm v))) (rlbl (perm v) u) b (fun x => x 9 = false) := by
    intro gs hFT u b v hC
    refine ⟨?_, by simp, ?_⟩
    · intro g hg
      simp only [List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      have := hFT g0 hg0
      simpa [rlblG] using this
    · intro x hx
      have key := rlbl_run (perm v) gs (List.ofFn x) (List.ofFn (x ∘ perm v)) (by simp) (by simp)
        (by
          intro k
          rw [ofFn_getD', ofFn_getD']
          by_cases hk : k < 10
          · have hr : rlbl (perm v) k = perm v ⟨k, hk⟩ := by simp [rlbl, hk]
            rw [hr, dif_pos (perm v ⟨k, hk⟩).isLt, dif_pos hk]
            rfl
          · have hr : rlbl (perm v) k = k := by simp [rlbl, hk]
            rw [hr, dif_neg hk, dif_neg hk]) u
      rw [key, hC (x ∘ perm v) (by simp [perm9, hx]), perm_aut]
  have h1_core : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (hFT : FT gs) (hlen : gs.length ≤ 17) (u : ℕ) (b : Bool) (hC : Comp gs u b (fun _ => True)), ∃ gs' u', FT gs' ∧ gs'.length ≤ 15 ∧ Comp gs' u' b (fun x => x 9 = false) := by
    intro gs hFT hlen u b hC
    by_cases h15 : gs.length ≤ 15
    · exact ⟨gs, u, hFT, h15, fun x _ => hC x trivial⟩
    by_cases h16 : gs.length = 16
    · obtain ⟨gs', u', h1, h2, h3⟩ := one_rem gs hFT u b hC
      exact ⟨gs', u', h1, by omega, h3⟩
    have h17 : gs.length = 17 := by omega
    by_cases hgood : ∃ v : Fin 10, ¬ bad gs v
    · obtain ⟨v, hv⟩ := hgood
      obtain ⟨gs'', u'', k1, k2, k3⟩ := good_two gs hFT u b hC v hv
      obtain ⟨r1, r2, r3⟩ := rlbl_comp gs'' k1 u'' b v k3
      exact ⟨_, _, r1, by omega, r3⟩
    · push Not at hgood
      obtain ⟨c, hc⟩ := first_gate gs hFT u b hC (by omega) hgood
      have hnc := nonconst_of_comp gs u b (fun _ => True) hC (by
        obtain ⟨x, x', _, _, h⟩ := PF_noncon 0
        exact ⟨x, x', trivial, trivial, h⟩)
      obtain ⟨m, r, hR, -⟩ := chain gs hFT u _ hnc _ 0 c rfl (by omega) hc
      obtain ⟨e1, e2, e3, -⟩ := erase_ok gs u b _ m r hFT hC hR
      obtain ⟨gs', u', f1, f2, f3⟩ := one_rem _ e1 _ b e3
      exact ⟨gs', u', f1, by omega, f3⟩

  have hC : Comp C.gates u b (fun _ => True) := by
    intro x _
    rw [hF]
    exact agrees x
  obtain ⟨gs,o,legal,len,computes⟩ := h1_core C.gates fan small u b hC
  obtain ⟨x,hx,hne⟩ := minor ⟨gs,o⟩ o b legal len
  apply hne
  have h := computes x hx
  rw [hF] at h
  exact h
end Peter17

namespace Reader7354
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def rho : Fin 10 → Fin 10 := ![9,6,8,5,7,4,1,3,0,2]
theorem invariant (x : Fin 10→Bool) : Peter17.target (x ∘ rho) = Peter17.target x := by
  have finite : ∀ a b c d e f g h i j : Bool,
     Peter17.target (![a,b,c,d,e,f,g,h,i,j] ∘ rho) = Peter17.target ![a,b,c,d,e,f,g,h,i,j] := by decide
  have eq : x = ![x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9] := by funext i; fin_cases i <;> rfl
  conv_lhs => rw [eq]
  exact (finite _ _ _ _ _ _ _ _ _ _).trans (congrArg Peter17.target eq.symm)
def ren (C : Circuit) : Circuit := ⟨C.gates.map (Copy.renameG rho 10),Copy.name rho 10 C.output⟩
theorem ren_ok (C : Circuit) (fan : FanInTwo C) : FanInTwo (ren C) := by
  intro g hg
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
  simpa [Copy.renameG] using fan a ha
theorem ren_eval (C : Circuit) (x : Fin 10→Bool) :
    (ren C).eval (List.ofFn x) = C.eval (List.ofFn (x ∘ rho)) := by
  have hh (p : Fin 10) : (List.ofFn x).getD (rho p).val false=(x ∘ rho) p := by fin_cases p <;> rfl
  have th := Copy.copy_val rho (List.ofFn x) (by simp) _ hh C
  exact th
def minor := ∀ (E:Circuit) (u:Nat) (b:Bool), FanInTwo E → E.size ≤ 15 →
  ∃ x : Fin 10 → Bool, x 9=false ∧ Peter17.signed b ((E.wires (List.ofFn x)).getD u false) ≠ Peter17.target x
theorem pin_from (floor : minor) : pinFloor := by
  intro C fan small
  obtain ⟨x,hx,ne⟩ := floor (ren C) (ren C).output false (ren_ok C fan)
    (by simpa [ren,Circuit.size] using small)
  refine ⟨x ∘ rho,hx,?_⟩
  rw [invariant]
  change (ren C).eval (List.ofFn x) ≠ Peter17.target x at ne
  rwa [ren_eval] at ne
theorem full_from (floor : minor) (C:Circuit) (fan : FanInTwo C) (small:C.size≤17) :
    ∃ x : Fin 10→Bool, C.eval (List.ofFn x ++ [x 0 && x 2]) ≠ Peter17.target x := by
  by_contra! correct
  by_cases freq : 2≤C.gates.countP touch
  · exact many (pin_from floor) C fan small freq correct
  · have ord : ordinary17 := fun D legal budget => Peter17.signed17With floor D D.output false legal budget
    exact few ord C fan small (by omega) correct
end Reader7354

end PEqualNP.Outside.L_meta_18804
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_18804 in
theorem PEqualNP.Outside.L_meta_18804 : have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size ≤ (17 : ℕ) → (∀ (x5 : Fin (10 : ℕ) → Bool), x2.eval (List.ofFn x5 ++ [x5 (0 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ))]) = x1 x5) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) (x8 : Bool), PEqualNP.MetaComplexity.FanInTwo x6 ∧ x6.size ≤ (15 : ℕ) ∧ ∀ (x9 : Fin (10 : ℕ) → Bool), x9 (9 : Fin (10 : ℕ)) = Bool.false → (if x8 = Bool.true then !(x6.wires (List.ofFn x9)).getD x7 Bool.false else (x6.wires (List.ofFn x9)).getD x7 Bool.false) = x1 x9 := by
  dsimp only
  intro C fan small good
  by_contra! no
  obtain ⟨x,hx⟩ := Reader7354.full_from no C fan small
  exact hx (good x)
