import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10796

namespace OneNot10797
open PEqualNP.CircuitLowerBounds
def original (x : Fin 7→Bool) : Bool := decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
def wires : List Gate := [⟨.or,[3,4]⟩,⟨.or,[0,6]⟩,⟨.or,[4,5]⟩,⟨.or,[1,5]⟩,⟨.or,[8,10]⟩,⟨.and,[8,10]⟩,⟨.or,[6,9]⟩,⟨.or,[2,12]⟩,⟨.and,[13,14]⟩,⟨.and,[7,11]⟩,⟨.or,[15,16]⟩]
def witness : Circuit := ⟨wires,17⟩
theorem eleven : wires.length=11 ∧ (∀ g∈wires,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2) := by
  constructor
  · rfl
  · intro g hg
    simp only [wires,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem witnessCorrect : ∀ x : Fin 7→Bool,witness.eval (List.ofFn x)=original x := by decide +kernel
def monotone (gs : List Gate) := ∀ g∈gs,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2
def fits (C : Circuit) := ∀ x : Fin 7→Bool,C.eval (List.ofFn x)=original x
def oneNot (gs : List Gate) := (∀ g∈gs,(g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2) ∧
  (∀ i j : Fin gs.length,(gs.get i).op=.not → (gs.get j).op=.not → i=j)
def Replacement (C : Circuit) := ∃ D : Circuit,monotone D.gates ∧ D.gates.length≤C.gates.length ∧ fits D
theorem large (C : Circuit) (big : 11≤C.gates.length) : Replacement C :=
  ⟨witness,eleven.2,(eleven.1.le.trans big),witnessCorrect⟩
end OneNot10797

namespace FreeAIG
abbrev Fn (α : Type*) := α → Bool
def neg {α} (f : Fn α) : Fn α := fun x => !(f x)
def meet {α} (a b : Fn α) : Fn α := fun x => a x && b x

inductive Avail {α : Type*} (S : Set (Fn α)) : Fn α → Prop where
  | src {f} : f∈S → Avail S f
  | const (b : Bool) : Avail S (fun _ => b)
  | neg {f} : Avail S f → Avail S (FreeAIG.neg f)

inductive Has {α : Type*} : Set (Fn α) → Nat → Fn α → Prop where
  | done {S k f} : Avail S f → Has S k f
  | step {S k a b f} : Avail S a → Avail S b → Has (insert (meet a b) S) k f → Has S (k+1) f

theorem Avail.lift {α : Type*} {S T : Set (Fn α)} (h : ∀g∈S,Avail T g) {f} (p : Avail S f) :
    Avail T f := by
  induction p with
  | src hs => exact h _ hs
  | const b => exact .const b
  | neg _ ih => exact .neg ih

theorem Avail.extend {α : Type*} {S : Set (Fn α)} {a f} (p : Avail S f) :
    Avail (insert a S) f := p.lift (fun _ hs=>.src (Set.mem_insert_of_mem _ hs))

theorem Avail.map {α β : Type*} {S : Set (Fn α)} {T : Set (Fn β)} (φ : β→α)
    (h : ∀g∈S,Avail T (g∘φ)) {f} (p : Avail S f) : Avail T (f∘φ) := by
  induction p with
  | src hs => exact h _ hs
  | const b => exact .const b
  | neg _ ih => exact .neg ih

theorem Has.map {α β : Type*} {S : Set (Fn α)} {T : Set (Fn β)} (φ : β→α)
    (h : ∀g∈S,Avail T (g∘φ)) {k f} (p : Has S k f) : Has T k (f∘φ) := by
  induction p generalizing T with
  | done hp => exact .done (hp.map φ h)
  | @step S k a b f ha hb _ ih =>
    apply Has.step (ha.map φ h) (hb.map φ h)
    apply ih
    rintro g (rfl|hg)
    · exact .src (Set.mem_insert _ _)
    · exact (h g hg).extend

def Inputs {n} : Set (Fn (Fin n→Bool)) := {g | ∃ i : Fin n,g=fun x=>x i}

end FreeAIG

namespace FreeAIG
theorem meetFalseR {α} (a : Fn α) : meet a (fun _=>false)=(fun _=>false) := by funext x;simp [meet]
theorem meetTrueR {α} (a : Fn α) : meet a (fun _=>true)=a := by funext x;simp [meet]
theorem meetFalseL {α} (b : Fn α) : meet (fun _=>false) b=(fun _=>false) := by funext x;simp [meet]
theorem meetTrueL {α} (b : Fn α) : meet (fun _=>true) b=b := by funext x;simp [meet]

def Restricted {α} (φ : α→α) (f : Fn α) := f∘φ=f ∨ ∃ b : Bool, f∘φ=fun _=>b

theorem Avail.restricted {α : Type*} {φ : α→α} {S : Set (Fn α)}
    (h : ∀g∈S,Restricted φ g) {f} (p : Avail S f) : Restricted φ f := by
  induction p with
  | src hs => exact h _ hs
  | const b => exact Or.inl rfl
  | @neg g _ ih =>
    rcases ih with eq|⟨b,eq⟩
    · exact Or.inl (congrArg FreeAIG.neg eq)
    · exact Or.inr ⟨!b,congrArg FreeAIG.neg eq⟩

theorem Has.save {α : Type*} {S T : Set (Fn α)} (φ : α→α) (mapS : ∀g∈S,Avail T (g∘φ))
    (good : ∀g∈S,Restricted φ g) {k f} (p : Has S k f) (hn : ¬Restricted φ f) :
    ∃ t, t+1≤k ∧ Has T t (f∘φ) := by
  induction p generalizing T with
  | done hp => exact (hn (hp.restricted good)).elim
  | @step S k a b f ha hb tail ih =>
    have ma := ha.map φ mapS
    have mb := hb.map φ mapS
    have finish (cheap : Avail T ((meet a b)∘φ)) : ∃ t, t+1≤k+1 ∧ Has T t (f∘φ) := by
      refine ⟨k,le_rfl,tail.map φ ?_⟩
      rintro g (rfl|hg)
      · exact cheap
      · exact mapS g hg
    rcases ha.restricted good with ea|⟨ba,ea⟩
    · rcases hb.restricted good with eb|⟨bb,eb⟩
      · have join : (meet a b)∘φ=meet a b := congrArg₂ meet ea eb
        obtain ⟨t,ht,sm⟩ := ih (T:=insert (meet (a∘φ) (b∘φ)) T) (by
          rintro g (rfl|hg)
          · exact .src (Set.mem_insert _ _)
          · exact (mapS g hg).extend) (by
          rintro g (rfl|hg)
          · exact Or.inl join
          · exact good g hg) hn
        exact ⟨t+1,by omega,.step ma mb sm⟩
      · apply finish
        change Avail T (meet (a∘φ) (b∘φ))
        rw [eb]
        cases bb
        · rw [meetFalseR];exact .const false
        · rw [meetTrueR];exact ma
    · apply finish
      change Avail T (meet (a∘φ) (b∘φ))
      rw [ea]
      cases ba
      · rw [meetFalseL];exact .const false
      · rw [meetTrueL];exact mb

theorem fixSave {n} (f : Fn (Fin n→Bool)) (i : Fin n) (b : Bool)
    (dep : ∃ x, f (Function.update x i b) ≠ f x)
    (nc : ∃ x x', f (Function.update x i b) ≠ f (Function.update x' i b))
    {k} (p : Has Inputs k f) :
    ∃ t, t+1≤k ∧ Has Inputs t (fun x=>f (Function.update x i b)) := by
  let φ : (Fin n→Bool)→(Fin n→Bool) := fun x=>Function.update x i b
  have other {j : Fin n} (ne : j≠i) : ((fun x : Fin n→Bool=>x j)∘φ)=(fun x=>x j) := by
    funext x;simp [φ,ne]
  have same : ((fun x : Fin n→Bool=>x i)∘φ)=(fun _=>b) := by funext x;simp [φ]
  apply p.save φ
  · rintro g ⟨j,rfl⟩
    by_cases e : j=i
    · subst j;rw [same];exact .const b
    · rw [other e];exact .src ⟨j,rfl⟩
  · rintro g ⟨j,rfl⟩
    by_cases e : j=i
    · subst j; exact Or.inr ⟨b,same⟩
    · exact Or.inl (other e)
  · rintro (eq|⟨v,eq⟩)
    · obtain ⟨x,h⟩ := dep
      exact h (congrFun eq x)
    · obtain ⟨x,x',h⟩ := nc
      exact h ((congrFun eq x).trans (congrFun eq x').symm)
end FreeAIG

namespace OneNot10797
def four (x : Fin 4→Bool) := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) ||
  (x 1 && x 2) || (x 1 && x 3) || (x 2 && x 3)
end OneNot10797

namespace FreeAIG
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def price : GateOp → Nat | .not => 0 | _ => 1
def binaryCount : List Gate → Nat
  | [] => 0
  | g::gs => price g.op + binaryCount gs

theorem leLength (gs : List Gate) : binaryCount gs ≤ gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases h:g.op <;> simp [binaryCount,h,price] <;> omega

theorem notDiscount {gs : List Gate} (h : ∃ g∈gs,g.op=.not) : binaryCount gs+1≤gs.length := by
  induction gs with
  | nil => simp at h
  | cons g gs ih =>
    obtain ⟨u,hu,op⟩ := h
    rcases List.mem_cons.mp hu with rfl|hg
    · simpa [binaryCount,op,price] using leLength gs
    · have hlt := ih ⟨u,hg,op⟩
      cases h:g.op <;> simp [binaryCount,h,price] <;> omega

theorem Has.bump {α : Type*} {S : Set (Fn α)} {k f} (p : Has S k f) : Has S (k+1) f := by
  induction p with
  | done h => exact .done h
  | step a b _ ih => exact .step a b ih

def applied {α} (g : Gate) (state : List (Fn α)) : Fn α := fun x =>
  g.op.eval (g.inputs.map (fun i => (state.getD i (fun _=>false)) x))
def run {α} (gs : List Gate) (state : List (Fn α)) : List (Fn α) :=
  gs.foldl (fun s g=>s++[applied g s]) state

theorem availGet {α : Type*} {S : Set (Fn α)} {st : List (Fn α)} (hs : ∀f∈st,Avail S f)
    (i : Nat) : Avail S (st.getD i (fun _=>false)) := by
  by_cases h : i<st.length
  · rw [List.getD_eq_getElem _ _ h]; exact hs _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (by omega)]; exact .const false

theorem Has.same {α : Type*} {S T : Set (Fn α)} {k f} (p : Has S k f) (h : ∀g∈S,Avail T g) :
    Has T k f := p.map id h

theorem gateCost {α : Type*} {S : Set (Fn α)} (g : Gate) (st : List (Fn α))
    (old : ∀f∈st,Avail S f)
    (legal : (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2)
    {f k} (tail : ∀ T : Set (Fn α), (∀ a∈st,Avail T a) → Avail T (applied g st) → Has T k f) :
    Has S (price g.op + k) f := by
  have base (A : Avail S (applied g st)) : Has S k f := tail S old A
  have ext (a : Fn α) : ∀u∈st,Avail (insert a S) u := fun u hu=>(old u hu).extend
  obtain ⟨op,len⟩ := legal
  cases g with | mk opg ins =>
  change opg=.and ∨ opg=.or ∨ opg=.not at op
  change ins.length≤2 at len
  match ins,len with
  | [],_ =>
    have free := base (Avail.const (opg.eval []))
    rcases op with rfl|rfl|rfl <;> simp [price,Nat.add_comm] <;> first | exact free.bump | exact free
  | [i],_ =>
    let a := st.getD i (fun _=>false)
    have ha : Avail S a := availGet old i
    rcases op with rfl|rfl|rfl
    · have e : applied ⟨.and,[i]⟩ st=a := by funext x;simp [applied,a,GateOp.eval]
      simpa [price,Nat.add_comm] using (base (e ▸ ha)).bump
    · have e : applied ⟨.or,[i]⟩ st=a := by funext x;simp [applied,a,GateOp.eval]
      simpa [price,Nat.add_comm] using (base (e ▸ ha)).bump
    · simpa [price] using base ha.neg
  | [i,j],_ =>
    let a := st.getD i (fun _=>false)
    let b := st.getD j (fun _=>false)
    have ha : Avail S a := availGet old i
    have hb : Avail S b := availGet old j
    rcases op with rfl|rfl|rfl
    · have e : applied ⟨.and,[i,j]⟩ st=meet a b := by funext x;simp [applied,a,b,meet,GateOp.eval]
      have h := tail (insert (meet a b) S) (ext _) (e ▸ Avail.src (Set.mem_insert _ _))
      simpa [price,Nat.add_comm] using Has.step ha hb h
    · have e : applied ⟨.or,[i,j]⟩ st=neg (meet (neg a) (neg b)) := by
        funext x;simp [applied,a,b,meet,neg,GateOp.eval]
      have h := tail (insert (meet (neg a) (neg b)) S) (ext _)
        (e ▸ (Avail.src (Set.mem_insert _ _)).neg)
      simpa [price,Nat.add_comm] using Has.step ha.neg hb.neg h
    · simpa [price] using base ha.neg

theorem listAIG {α : Type*} (gs : List Gate) (legal : ∀g∈gs,
    (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2)
    (st : List (Fn α)) (S : Set (Fn α)) (old : ∀f∈st,Avail S f) (o) :
    Has S (binaryCount gs) ((run gs st).getD o (fun _=>false)) := by
  induction gs generalizing st S with
  | nil => exact .done (availGet old o)
  | cons g gs ih =>
    apply gateCost g st old (legal g (by simp))
    intro T prev h
    apply ih (fun u hu=>legal u (by simp [hu])) (st++[applied g st]) T
    intro u hu
    rcases List.mem_append.mp hu with u0|u1
    · exact prev u u0
    · have eq := List.mem_singleton.mp u1;exact eq ▸ h

theorem mapRun {α} (gs : List Gate) (st : List (Fn α)) (x : α) :
    (run gs st).map (fun a=>a x) =
    gs.foldl (fun s g=>s++[g.op.eval (g.inputs.map (fun j=>s.getD j false))]) (st.map (fun a=>a x)) := by
  induction gs generalizing st with
  | nil => rfl
  | cons g gs ih =>
    simp only [run,List.foldl_cons] at ih ⊢
    rw [ih]
    congr 1
    simp only [List.map_append,List.map_cons,List.map_nil,List.append_cancel_left_eq]
    congr 2
    unfold applied
    congr 1
    apply List.map_congr_left
    intro i _
    exact (List.getD_map st (fun _=>false) (n:=i) (fun a : Fn α=>a x)).symm

theorem circuitAIG {n} (C : Circuit) (legal : ∀g∈C.gates,
    (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2) :
    Has Inputs (binaryCount C.gates) (fun x : Fin n→Bool=>C.eval (List.ofFn x)) := by
  let st : List (Fn (Fin n→Bool)) := List.ofFn (fun i x=>x i)
  have h := listAIG C.gates legal st Inputs (by
    intro f hf
    obtain ⟨i,eq⟩ := List.mem_ofFn.mp hf
    exact .src ⟨i,eq.symm⟩) C.output
  convert h using 1
  funext x
  have hst : st.map (fun a=>a x)=List.ofFn x := by simp [st,List.map_ofFn,Function.comp_def]
  have eq := mapRun C.gates st x
  rw [hst] at eq
  change (C.wires (List.ofFn x)).getD C.output false=_
  rw [show C.wires (List.ofFn x)=(run C.gates st).map (fun a=>a x) from eq.symm]
  exact List.getD_map _ (fun _=>false) (n:=C.output) (fun a : Fn (Fin n→Bool)=>a x)

end FreeAIG

namespace OneNot10797
open FreeAIG PEqualNP.CircuitLowerBounds
theorem binaryFloor (fourLower : ∀t, Has Inputs t four → 7≤t)
    (squeeze : ∀{k},Has Inputs k original → ∃ t,t+3≤k ∧ Has Inputs t four)
    (C : Circuit) (lg : ∀g∈C.gates,(g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2)
    (sem : fits C) : 10 ≤ binaryCount C.gates := by
  have h := circuitAIG (n:=7) C lg
  rw [funext sem] at h
  obtain ⟨k,save,core⟩ := squeeze h
  have lower := fourLower k core
  omega

theorem allNotReplacement (fourLower : ∀t, Has Inputs t four → 7≤t)
    (squeeze : ∀{k},Has Inputs k original → ∃ t,t+3≤k ∧ Has Inputs t four)
    (C : Circuit) (lg : ∀g∈C.gates,(g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2)
    (sem : fits C) : Replacement C := by
  by_cases ex : ∃g∈C.gates,g.op=.not
  · exact large C ((Nat.add_le_add_right (binaryFloor fourLower squeeze C lg sem) 1).trans (notDiscount ex))
  · refine ⟨C,?_,le_rfl,sem⟩
    intro g hg
    obtain ⟨op,len⟩ := lg g hg
    exact ⟨op.elim Or.inl (fun h=>h.elim Or.inr (fun h=>(ex ⟨g,hg,h⟩).elim)),len⟩
end OneNot10797

namespace OneNot10797
open FreeAIG
def fixed (f : Fn (Fin 7→Bool)) (y : Fin 7) : Fn (Fin 7→Bool) := fun x=>f (Function.update x y false)
def after0 := fixed original 0
def after1 := fixed after0 1
def after3 := fixed after1 3
def sample (m : Nat) (i : Fin 7) := m.testBit i.val
def embed (x : Fin 4→Bool) : Fin 7→Bool := ![false,false,x 0,false,x 1,x 2,x 3]

theorem seed0 : fixed original 0 (sample 17) ≠ original (sample 17) := by decide +kernel
theorem seed1 : after1 (sample 18) ≠ after0 (sample 18) := by decide +kernel
theorem seed3 : after3 (sample 40) ≠ after1 (sample 40) := by decide +kernel
theorem sep0 : after0 (sample 0) ≠ after0 (sample 48) := by decide +kernel
theorem sep1 : after1 (sample 0) ≠ after1 (sample 48) := by decide +kernel
theorem sep3 : after3 (sample 0) ≠ after3 (sample 48) := by decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 32768 in
theorem embedEq : ∀ x : Fin 4→Bool, after3 (embed x)=four x := by decide +kernel

theorem pay (f g : Fn (Fin 7→Bool)) (i : Fin 7) (eq : g=fixed f i)
    (z u v : Fin 7→Bool) (dep : g z ≠ f z) (nc : g u ≠ g v)
    {k} (h : Has Inputs k f) : ∃t,t+1≤k ∧ Has Inputs t g := by
  subst g
  exact fixSave f i false ⟨z,dep⟩ ⟨u,v,nc⟩ h

theorem squeeze0 {k} (h : Has Inputs k original) : ∃ t,t+1≤k ∧ Has Inputs t after0 :=
  pay original after0 0 rfl (sample 17) (sample 0) (sample 48) seed0 sep0 h
theorem squeeze1 {k} (h : Has Inputs k after0) : ∃ t,t+1≤k ∧ Has Inputs t after1 :=
  pay after0 after1 1 rfl (sample 18) (sample 0) (sample 48) seed1 sep1 h
theorem squeeze3 {k} (h : Has Inputs k after1) : ∃ t,t+1≤k ∧ Has Inputs t after3 :=
  pay after1 after3 3 rfl (sample 40) (sample 0) (sample 48) seed3 sep3 h

theorem inputMap : ∀ g∈Inputs,Avail Inputs (g∘embed) := by
  rintro g ⟨i,rfl⟩
  fin_cases i
  · exact .const false
  · exact .const false
  · exact .src ⟨0,rfl⟩
  · exact .const false
  · exact .src ⟨1,rfl⟩
  · exact .src ⟨2,rfl⟩
  · exact .src ⟨3,rfl⟩
theorem compress4 {k} (h : Has Inputs k after3) : Has Inputs k four := by
  have sm : Has Inputs k (after3∘embed) := h.map embed inputMap
  have eq : after3∘embed=four := funext embedEq
  exact eq ▸ sm
theorem triple {k} (h : Has Inputs k original) : ∃ t,t+3≤k ∧ Has Inputs t four := by
  obtain ⟨a,ha,p0⟩ := squeeze0 h
  obtain ⟨b,hb,p1⟩ := squeeze1 p0
  obtain ⟨c,hc,p3⟩ := squeeze3 p1
  exact ⟨c,by omega,compress4 p3⟩
end OneNot10797

namespace K4Core
abbrev T := BitVec 16
def tgt : T := 65256
def neg (x:T) := ~~~x
def sat (s:List T) : List T := 0 :: 65535 :: (s ++ s.map neg)
def combs (s:List T) := (sat s).flatMap fun a => (sat s).map fun b => a &&& b
inductive Reach : Nat → List T → T → Prop where
  | done {s z} : z∈sat s → Reach 0 s z
  | step {k s g z} : g∈combs s → Reach k (g::s) z → Reach (k+1) s z

theorem src {s t : List T} (h : ∀ x∈s, x∈t) {x} (hx : x∈sat s) : x∈sat t := by
  simp only [sat,List.mem_cons,List.mem_append,List.mem_map] at hx ⊢
  rcases hx with h0|h1|h2|⟨y,hy,he⟩
  · exact Or.inl h0
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl (h _ h2)))
  · exact Or.inr (Or.inr (Or.inr ⟨y,h y hy,he⟩))

theorem negmem {s : List T} {x} (h : x∈sat s) : neg x∈sat s := by
  simp only [sat,List.mem_cons,List.mem_append,List.mem_map] at h ⊢
  rcases h with rfl|rfl|h|⟨y,hy,rfl⟩
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inr ⟨_,h,rfl⟩))
  · exact Or.inr (Or.inr (Or.inl (by simpa [neg] using hy)))

theorem ext {a:T} {s:List T} {x} (h : x∈sat (a::s)) : x∈sat s ∨ x=a ∨ x=neg a := by
  simpa [sat,List.mem_append, or_assoc, or_left_comm, or_comm] using h

theorem meetmem {s:List T} {a b} (ha:a∈sat s) (hb:b∈sat s) : a &&& b ∈ combs s := by
  exact List.mem_flatMap.mpr ⟨a,ha,List.mem_map.mpr ⟨b,hb,rfl⟩⟩

def fits (v p n : T) : Bool := v &&& p == p && v &&& n == 0

def clash (s : List T) (p n:T) : Bool :=
  let chosen := s.filter fun x => x &&& p == p
  chosen.any fun a => chosen.any fun b => a &&& b &&& n == 0

def one (s : List T) (p n:T) := clash s p n || clash s n p

def two (s : List T) (p n:T) : Bool :=
  let l := sat s
  l.any fun a => ((a &&& p == p) && one l p (a &&& n)) ||
                  ((a &&& n == n) && one l n (a &&& p))

theorem clash_of (s:List T) {a b p n:T} (ha:a∈s) (hb:b∈s)
    (hf:fits (a &&& b) p n=true) : clash s p n=true := by
  simp only [fits,Bool.and_eq_true,beq_iff_eq] at hf
  have hpa : a &&& p = p := by
    calc
      a &&& p = a &&& (a &&& b &&& p) := congrArg (a &&& ·) hf.1.symm
      _ = (a &&& a) &&& b &&& p := by ac_rfl
      _ = p := by simpa using hf.1
  have hpb : b &&& p = p := by
    calc
      b &&& p = b &&& (a &&& b &&& p) := congrArg (b &&& ·) hf.1.symm
      _ = a &&& (b &&& b) &&& p := by ac_rfl
      _ = p := by simpa using hf.1
  simp only [clash,List.any_eq_true,List.mem_filter,beq_iff_eq]
  exact ⟨a,⟨ha,hpa⟩,b,⟨hb,hpb⟩,hf.2⟩

theorem neg_eq_all (x p:T) : neg x &&& p = p ↔ x &&& p = 0 := by
  constructor <;> intro h <;> ext i hi
  all_goals
    have hh := congrArg (fun z : T => z[i]) h
    simp [neg] at hh ⊢
    cases h₁:x[i] <;> cases h₂:p[i] <;> simp_all

theorem fits_neg_iff (a p n:T) : fits (neg a) p n=true ↔ fits a n p=true := by
  simp only [fits,Bool.and_eq_true,beq_iff_eq,neg_eq_all]
  have h := neg_eq_all (neg a) n
  simp only [neg,BitVec.not_not] at h
  change (_ ∧ ~~~a &&& n = 0) ↔ _
  rw [←h, and_comm]

theorem fitMeet (a b p n:T) (hf:fits (a &&& b) p n=true) :
    a &&& p = p ∧ fits b p (a &&& n)=true := by
  simp only [fits,Bool.and_eq_true,beq_iff_eq] at hf ⊢
  have f : ∀ u v:T, u &&& v &&& p = p → u &&& p=p := by
    intro u v hp
    calc
      u &&& p = u &&& (u &&& v &&& p) := congrArg (u &&& ·) hp.symm
      _ = (u &&& u) &&& v &&& p := by ac_rfl
      _ = p := by simpa using hp
  exact ⟨f a b hf.1, f b a (by rw [BitVec.and_comm b a]; exact hf.1),
    (by calc
          b &&& (a &&& n) = a &&& b &&& n := by ac_rfl
          _ = 0 := hf.2)⟩

theorem srcOne {s:List T} {z p n:T} (hz:z∈sat s) (hf:fits z p n=true) :
    one (sat s) p n=true := by
  unfold one
  rw [Bool.or_eq_true]
  apply Or.inl
  exact clash_of _ hz hz (by simpa using hf)

theorem newOne {s:List T} {g z p n:T} (hg:g∈combs s) (hz:z∈sat (g::s))
    (hf:fits z p n=true) : one (sat s) p n=true := by
  rcases ext hz with old|rfl|rfl
  · exact srcOne old hf
  all_goals
    obtain ⟨a,ha,hh⟩ := List.mem_flatMap.mp hg
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hh
  · unfold one
    rw [Bool.or_eq_true]
    exact Or.inl (clash_of _ ha hb hf)
  · unfold one
    rw [Bool.or_eq_true]
    exact Or.inr (clash_of _ ha hb ((fits_neg_iff _ _ _).mp hf))

theorem fac {s:List T} {g x y:T} (hx:x∈sat (g::s)) (hy:y∈sat (g::s)) :
    ∃ a∈sat s, ∃ b∈sat (g::s), x &&& y=a &&& b := by
  rcases ext hx with h|p
  · exact ⟨x,h,y,hy,rfl⟩
  rcases ext hy with h|q
  · exact ⟨y,h,x,hx,BitVec.and_comm _ _⟩
  have hw : BitVec.allOnes 16 ∈ sat s := by simp [sat,show BitVec.allOnes 16 = 65535 by rfl]
  refine ⟨_,hw,x &&& y,?_,BitVec.allOnes_and.symm⟩
  rcases p with rfl|rfl <;> rcases q with rfl|rfl <;> simp [neg,sat,BitVec.and_comm]

theorem two_from {s:List T} {g x p n:T} (hg:g∈combs s) (hx:x∈sat (g::s))
    (h : fits x p n=true) : two s p n=true := by
  have hw : BitVec.allOnes 16 ∈ sat s := by simp [sat,show BitVec.allOnes 16 = 65535 by rfl]
  simp only [two,List.any_eq_true,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq]
  exact ⟨_,hw,Or.inl ⟨BitVec.allOnes_and,by change one (sat s) p (BitVec.allOnes 16 &&& n)=true; rw [BitVec.allOnes_and]; exact newOne hg hx h⟩⟩

theorem two_from_prod {s:List T} {g x y p n:T} (hg:g∈combs s)
    (hx:x∈sat (g::s)) (hy:y∈sat (g::s)) (h:fits (x &&& y) p n=true) :
    two s p n=true := by
  obtain ⟨a,ha,b,hb,e⟩ := fac hx hy
  rw [e] at h
  obtain ⟨hp,hf⟩ := fitMeet a b p n h
  simp only [two,List.any_eq_true,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq]
  exact ⟨a,ha,Or.inl ⟨hp,newOne hg hb hf⟩⟩

theorem two_swap {s:List T} {p n:T} : two s p n = two s n p := by
  simp only [two,Bool.or_comm]

theorem two_all {s:List T} {g h z p n:T} (hg:g∈combs s) (hh:h∈combs (g::s))
    (hz:z∈sat (h::g::s)) (hf:fits z p n=true) : two s p n=true := by
  rcases ext hz with old|rfl|rfl
  · exact two_from hg old hf
  all_goals
    obtain ⟨a,ha,ww⟩ := List.mem_flatMap.mp hh
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ww
  · exact two_from_prod hg ha hb hf
  · rw [two_swap]
    exact two_from_prod hg ha hb ((fits_neg_iff _ _ _).mp hf)
def pack {n:Nat} (f : Fin n→Bool) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (by simp)

theorem pack_get {n:Nat} (f : Fin n→Bool) (i:Fin n) : (pack f)[i.val] = f i := by
  have h : (BitVec.ofBoolListLE (List.ofFn f)).getLsbD i.val = f i := by
    rw [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD]
    simp
  exact h

def ren (π: Fin 16→Fin 16) (x:T) : T := pack fun i => x[(π i).val]

theorem ren_get (π) (x:T) (i:Nat) (hi:i<16) :
    (ren π x)[i] = x[(π ⟨i,hi⟩).val] := pack_get _ ⟨i,hi⟩

theorem ren_meet (π) (x y:T) : ren π (x &&& y) = ren π x &&& ren π y := by
  ext i hi
  simp only [ren_get,BitVec.getElem_and]

theorem ren_neg (π) (x:T) : ren π (neg x) = neg (ren π x) := by
  ext i hi
  simp only [ren_get,neg,BitVec.getElem_not]

theorem transfer {s t:List T} {k} {π : Fin 16→Fin 16}
    (h:∀ x∈sat s,ren π x∈sat t) {z} (hs:Reach k s z) : Reach k t (ren π z) := by
  induction hs generalizing t with
  | done hx => exact .done (h _ hx)
  | @step k s g z hg _ ih =>
    obtain ⟨a,ha,hh⟩ := List.mem_flatMap.mp hg
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hh
    apply Reach.step (meetmem (h _ ha) (h _ hb))
    apply ih
    intro x hx
    rcases ext hx with old|rfl|rfl
    · exact src (fun v hv => List.mem_cons_of_mem _ hv) (h _ old)
    · rw [ren_meet]
      simp [sat]
    · rw [ren_neg,ren_meet]
      apply negmem
      simp [sat]
def finish (s:List T) : Bool := (combs s).any fun g => two (g::s) tgt (neg tgt)
theorem finishLower {s:List T} (h:finish s=false) : ¬Reach 3 s tgt := by
  intro hr
  cases hr with | step hg h1 =>
    cases h1 with | step hh h2 =>
      cases h2 with | step hi h3 =>
        cases h3 with | done hz =>
          have t := two_all hh hi hz (by decide : fits tgt tgt (neg tgt)=true)
          have f : finish s = true := List.any_eq_true.mpr ⟨_,hg,t⟩
          simp_all
end K4Core

namespace K4Orbit
open K4Core
def stages3 : List (List T) := [
  [43690,52428,61680,65280],
  [170,43690,52428,61680,65280],
  [34952,43690,52428,61680,65280],
  [43690,52428,61166,61680,65280],
  [10,170,43690,52428,61680,65280],
  [10,43690,52428,61680,65280,65520],
  [136,170,43690,52428,61680,65280],
  [136,34952,43690,52428,61680,65280],
  [170,204,43690,52428,61680,65280],
  [170,2570,43690,52428,61680,65280],
  [170,3084,43690,52428,61680,65280],
  [170,3840,43690,52428,61680,65280],
  [170,21760,43690,52428,61680,65280],
  [170,34952,43690,52428,61680,65280],
  [170,43520,43690,52428,61680,65280],
  [170,43690,49344,52428,61680,65280],
  [170,43690,52224,52428,61680,65280],
  [170,43690,52292,52428,61680,65280],
  [170,43690,52428,52462,61680,65280],
  [170,43690,52428,61166,61680,65280],
  [170,43690,52428,61680,64764,65280],
  [170,43690,52428,61680,65280,65450],
  [170,43690,52428,61680,65280,65484],
  [238,43690,52428,61166,61680,65280],
  [2730,43690,52428,61440,61680,65280],
  [32896,34952,43690,52428,61680,65280],
  [34952,41120,43690,52428,61680,65280],
  [34952,43690,52428,61166,61680,65280],
  [34952,43690,52428,61440,61680,65280],
  [34952,43690,52428,61680,63736,65280],
  [34952,43690,52428,61680,64250,65280],
  [34952,43690,52428,61680,65280,65520],
  [43176,43690,52428,61680,64764,65280],
  [43690,52428,61166,61680,64250,65280],
  [43690,52428,61166,61680,65278,65280],
  [43690,52428,61166,61680,65280,65520],
  [2,10,170,43690,52428,61680,65280],
  [2,10,43690,52428,61680,65280,65520],
  [2,170,43690,52428,61680,64764,65280],
  [2,43690,52428,61680,64764,65280,65532],
  [8,10,170,43690,52428,61680,65280],
  [8,10,43690,52428,61680,65280,65520],
  [8,136,170,43690,52428,61680,65280],
  [8,136,34952,43690,52428,61680,65280],
  [8,170,3084,43690,52428,61680,65280],
  [8,34952,43690,52428,61680,65280,65520],
  [10,12,43690,52428,61680,65280,65520],
  [10,34,170,43690,52428,61680,65280],
  [10,136,170,43690,52428,61680,65280],
  [10,160,170,43690,52428,61680,65280],
  [10,170,204,43690,52428,61680,65280],
  [10,170,240,43690,52428,61680,65280],
  [10,170,2570,43690,52428,61680,65280],
  [10,170,3084,43690,52428,61680,65280],
  [10,170,3840,43690,52428,61680,65280],
  [10,170,8738,43690,52428,61680,65280],
  [10,170,12336,43690,52428,61680,65280],
  [10,170,13056,43690,52428,61680,65280],
  [10,170,17476,43690,52428,61680,65280],
  [10,170,20560,43690,52428,61680,65280],
  [10,170,21760,43690,52428,61680,65280],
  [10,170,34952,43690,52428,61680,65280],
  [10,170,41120,43690,52428,61680,65280],
  [10,170,43520,43690,52428,61680,65280],
  [10,170,43680,43690,52428,61680,65280],
  [10,170,43690,49344,52428,61680,65280],
  [10,170,43690,52224,52428,61680,65280],
  [10,170,43690,52292,52428,61680,65280],
  [10,170,43690,52420,52428,61680,65280],
  [10,170,43690,52428,52430,61680,65280],
  [10,170,43690,52428,52462,61680,65280],
  [10,170,43690,52428,61166,61680,65280],
  [10,170,43690,52428,61440,61680,65280],
  [10,170,43690,52428,61520,61680,65280],
  [10,170,43690,52428,61680,61690,65280],
  [10,170,43690,52428,61680,64250,65280],
  [10,170,43690,52428,61680,64764,65280],
  [10,170,43690,52428,61680,65280,65290],
  [10,170,43690,52428,61680,65280,65450],
  [10,170,43690,52428,61680,65280,65484],
  [10,170,43690,52428,61680,65280,65520],
  [10,204,43690,52428,61680,65280,65520],
  [10,240,43530,43690,52428,61680,65280],
  [10,240,43690,52428,61680,65280,65520],
  [10,250,43690,52428,61680,64250,65280],
  [10,8738,43690,52428,61680,65280,65520],
  [10,12336,43690,52428,61680,65280,65520],
  [10,13104,43690,52428,61680,65280,65520],
  [10,17476,43690,52428,61680,65280,65520],
  [10,20560,43690,52428,61680,65280,65520],
  [10,21840,43690,52428,61680,65280,65520],
  [10,34952,43690,52428,61680,65280,65520],
  [10,41120,43690,52428,61680,65280,65440],
  [10,41120,43690,52428,61680,65280,65520],
  [10,43680,43690,52428,61680,65280,65520],
  [10,43690,49344,52428,61680,65280,65520],
  [10,43690,52416,52428,61680,65280,65520],
  [10,43690,52420,52428,61680,65280,65520],
  [10,43690,52428,52430,61680,65280,65520],
  [10,43690,52428,61166,61680,65280,65520],
  [10,43690,52428,61440,61680,65280,65520],
  [10,43690,52428,61680,61690,65280,65520],
  [10,43690,52428,61680,64250,65280,65520],
  [10,43690,52428,61680,64764,65280,65520],
  [10,43690,52428,61680,65280,65520,65530],
  [10,43690,52428,61680,65280,65520,65532],
  [14,238,43690,52428,61166,61680,65280],
  [14,43690,52428,61166,61680,65280,65520],
  [42,170,43690,49344,52428,61680,65280],
  [42,10794,43690,49344,52428,61680,65280],
  [42,43690,49344,52428,61680,65280,65472],
  [128,136,170,43690,52428,61680,65280],
  [128,136,34952,43690,52428,61680,65280],
  [128,170,43690,49344,52428,61680,65280],
  [128,32896,34952,43690,52428,61680,65280],
  [136,160,170,43690,52428,61680,65280],
  [136,170,204,43690,52428,61680,65280],
  [136,170,240,43690,52428,61680,65280],
  [136,170,2570,43690,52428,61680,65280],
  [136,170,3084,43690,52428,61680,65280],
  [136,170,3840,43690,52428,61680,65280],
  [136,170,8738,43690,52428,61680,65280],
  [136,170,12336,43690,52428,61680,65280],
  [136,170,13056,43690,52428,61680,65280],
  [136,170,17476,43690,52428,61680,65280],
  [136,170,20560,43690,52428,61680,65280],
  [136,170,21760,43690,52428,61680,65280],
  [136,170,34952,43690,52428,61680,65280],
  [136,170,41120,43690,52428,61680,65280],
  [136,170,43520,43690,52428,61680,65280],
  [136,170,43554,43690,52428,61680,65280],
  [136,170,43690,49344,52428,61680,65280],
  [136,170,43690,52224,52428,61680,65280],
  [136,170,43690,52292,52428,61680,65280],
  [136,170,43690,52428,52462,61680,65280],
  [136,170,43690,52428,61166,61680,65280],
  [136,170,43690,52428,61440,61680,65280],
  [136,170,43690,52428,61520,61680,65280],
  [136,170,43690,52428,61552,61680,65280],
  [136,170,43690,52428,61680,61688,65280],
  [136,170,43690,52428,61680,61690,65280],
  [136,170,43690,52428,61680,64250,65280],
  [136,170,43690,52428,61680,64764,65280],
  [136,170,43690,52428,61680,65280,65416],
  [136,170,43690,52428,61680,65280,65450],
  [136,170,43690,52428,61680,65280,65484],
  [136,170,43690,52428,61680,65280,65520],
  [136,240,34952,43690,52428,61680,65280],
  [136,2056,34952,43690,52428,61680,65280],
  [136,2570,34952,43690,52428,61680,65280],
  [136,3840,34952,43690,52428,61680,65280],
  [136,8738,34952,43690,52428,61680,65280],
  [136,8738,43690,52428,61680,65280,65314],
  [136,8874,43690,52224,52428,61680,65280],
  [136,12336,34952,43690,52428,61680,65280],
  [136,13056,34952,43690,52428,61680,65280],
  [136,28784,34952,43690,52428,61680,65280],
  [136,30464,34952,43690,52428,61680,65280],
  [136,32896,34952,43690,52428,61680,65280],
  [136,34816,34952,43690,52428,61680,65280],
  [136,34952,41120,43690,52428,61680,65280],
  [136,34952,43520,43690,52428,61680,65280],
  [136,34952,43554,43690,52428,61680,65280],
  [136,34952,43690,52428,61166,61680,65280],
  [136,34952,43690,52428,61440,61680,65280],
  [136,34952,43690,52428,61552,61680,65280],
  [136,34952,43690,52428,61680,61688,65280],
  [136,34952,43690,52428,61680,63736,65280],
  [136,34952,43690,52428,61680,64250,65280],
  [136,34952,43690,52428,61680,65280,65416],
  [136,34952,43690,52428,61680,65280,65450],
  [136,34952,43690,52428,61680,65280,65520],
  [136,43656,43690,52428,61680,65280,65484],
  [138,170,12336,43690,52428,61680,65280],
  [138,12336,35466,43690,52428,61680,65280],
  [138,12336,43690,52428,61680,65280,65328],
  [168,170,43690,52428,61680,64764,65280],
  [168,252,43690,52428,61680,64764,65280],
  [168,43176,43690,52428,61680,64764,65280],
  [170,204,238,43690,52428,61680,65280],
  [170,204,240,43690,52428,61680,65280],
  [170,204,2570,43690,52428,61680,65280],
  [170,204,3840,43690,52428,61680,65280],
  [170,204,8738,43690,52428,61680,65280],
  [170,204,12336,43690,52428,61680,65280],
  [170,204,13056,43690,52428,61680,65280],
  [170,204,34952,43690,52428,61680,65280],
  [170,204,41120,43690,52428,61680,65280],
  [170,204,43520,43690,52428,61680,65280],
  [170,204,43554,43690,52428,61680,65280],
  [170,204,43690,43758,52428,61680,65280],
  [170,204,43690,52428,61166,61680,65280],
  [170,204,43690,52428,61440,61680,65280],
  [170,204,43690,52428,61488,61680,65280],
  [170,204,43690,52428,61680,61690,65280],
  [170,204,43690,52428,61680,64250,65280],
  [170,204,43690,52428,61680,65280,65450],
  [170,204,43690,52428,61680,65280,65520],
  [170,238,43690,52428,52462,61680,65280],
  [170,238,43690,52428,61166,61680,65280],
  [170,252,43690,52428,61680,64764,65280],
  [170,2570,2730,43690,52428,61680,65280],
  [170,2570,8738,43690,52428,61680,65280],
  [170,2570,12336,43690,52428,61680,65280],
  [170,2570,17476,43690,52428,61680,65280],
  [170,2570,20560,43690,52428,61680,65280],
  [170,2570,34952,43690,52428,61680,65280],
  [170,2570,41120,43690,52428,61680,65280],
  [170,2570,43690,49344,52428,61680,65280],
  [170,2570,43690,50372,52428,61680,65280],
  [170,2570,43690,52428,52462,61680,65280],
  [170,2570,43690,52428,61166,61680,65280],
  [170,2570,43690,52428,61440,61680,65280],
  [170,2570,43690,52428,61520,61680,65280],
  [170,2570,43690,52428,61680,61690,65280],
  [170,2570,43690,52428,61680,64250,65280],
  [170,2570,43690,52428,61680,64764,65280],
  [170,2570,43690,52428,61680,65280,65520],
  [170,2730,43690,52428,61440,61680,65280],
  [170,2730,43690,52428,61520,61680,65280],
  [170,3084,3246,43690,52428,61680,65280],
  [170,3084,12336,43690,52428,61680,65280],
  [170,3084,13056,43690,52428,61680,65280],
  [170,3084,34952,43690,52428,61680,65280],
  [170,3084,41120,43690,52428,61680,65280],
  [170,3084,41634,43690,52428,61680,65280],
  [170,3084,43520,43690,52428,61680,65280],
  [170,3084,43690,44718,52428,61680,65280],
  [170,3084,43690,52428,61166,61680,65280],
  [170,3084,43690,52428,61440,61680,65280],
  [170,3084,43690,52428,61520,61680,65280],
  [170,3084,43690,52428,61680,61690,65280],
  [170,3084,43690,52428,61680,64250,65280],
  [170,3084,43690,52428,61680,64764,65280],
  [170,3084,43690,52428,61680,65280,65520],
  [170,3086,43690,52428,52462,61680,65280],
  [170,3212,43690,52428,61520,61680,65280],
  [170,3276,43690,52428,61440,61680,65280],
  [170,3598,43690,52428,61166,61680,65280],
  [170,3840,4010,43690,52428,61680,65280],
  [170,3840,20560,43690,52428,61680,65280],
  [170,3840,34952,43690,52428,61680,65280],
  [170,3840,41120,43690,52428,61680,65280],
  [170,3840,41130,43690,52428,61680,65280],
  [170,3840,43520,43690,52428,61680,65280],
  [170,3840,43690,44970,52428,61680,65280],
  [170,3840,43690,49344,52428,61680,65280],
  [170,3840,43690,49356,52428,61680,65280],
  [170,3840,43690,52224,52428,61680,65280],
  [170,3840,43690,52292,52428,61680,65280],
  [170,3840,43690,52428,52462,61680,65280],
  [170,3840,43690,52428,53196,61680,65280],
  [170,3840,43690,52428,61166,61680,65280],
  [170,3840,43690,52428,61440,61680,65280],
  [170,3840,43690,52428,61520,61680,65280],
  [170,3840,43690,52428,61680,61690,65280],
  [170,3840,43690,52428,61680,64250,65280],
  [170,3840,43690,52428,61680,64764,65280],
  [170,3840,43690,52428,61680,65280,65450],
  [170,3840,43690,52428,61680,65280,65484],
  [170,3840,43690,52428,61680,65280,65520],
  [170,3850,43690,52428,61680,65280,65450],
  [170,3852,43690,52428,61680,65280,65484],
  [170,10794,43690,49344,52428,61680,65280],
  [170,16128,43690,49344,52428,61680,65280],
  [170,17612,43520,43690,52428,61680,65280],
  [170,19532,41120,43690,52428,61680,65280],
  [170,21588,43690,52428,61680,64764,65280],
  [170,21760,21930,43690,52428,61680,65280],
  [170,21760,34952,43690,52428,61680,65280],
  [170,21760,35020,43690,52428,61680,65280],
  [170,21760,43520,43690,52428,61680,65280],
  [170,21760,43690,49344,52428,61680,65280],
  [170,21760,43690,52428,52462,61680,65280],
  [170,21760,43690,52428,61166,61680,65280],
  [170,21760,43690,52428,61680,64764,65280],
  [170,21760,43690,52428,61680,65280,65450],
  [170,21828,43690,52428,61680,65280,65484],
  [170,24320,41120,43690,52428,61680,65280],
  [170,32896,34952,43690,52428,61680,65280],
  [170,32896,43690,49344,52428,61680,65280],
  [170,34816,34952,43690,52428,61680,65280],
  [170,34816,43520,43690,52428,61680,65280],
  [170,34816,43690,52224,52428,61680,65280],
  [170,34816,43690,52292,52428,61680,65280],
  [170,34952,34986,43690,52428,61680,65280],
  [170,34952,41120,43690,52428,61680,65280],
  [170,34952,43520,43690,52428,61680,65280],
  [170,34952,43690,49344,52428,61680,65280],
  [170,34952,43690,52224,52428,61680,65280],
  [170,34952,43690,52292,52428,61680,65280],
  [170,34952,43690,52428,52462,61680,65280],
  [170,34952,43690,52428,61166,61680,65280],
  [170,34952,43690,52428,61440,61680,65280],
  [170,34952,43690,52428,61520,61680,65280],
  [170,34952,43690,52428,61680,61690,65280],
  [170,34952,43690,52428,61680,63736,65280],
  [170,34952,43690,52428,61680,64250,65280],
  [170,34952,43690,52428,61680,64764,65280],
  [170,34952,43690,52428,61680,65280,65416],
  [170,34952,43690,52428,61680,65280,65450],
  [170,34952,43690,52428,61680,65280,65484],
  [170,34952,43690,52428,61680,65280,65520],
  [170,34986,43690,52428,52462,61680,65280],
  [170,43176,43690,52428,61680,64764,65280],
  [170,43520,43690,49344,52428,61680,65280],
  [170,43520,43690,52224,52428,61680,65280],
  [170,43520,43690,52292,52428,61680,65280],
  [170,43520,43690,52428,52462,61680,65280],
  [170,43520,43690,52428,61132,61680,65280],
  [170,43520,43690,52428,61166,61680,65280],
  [170,43520,43690,52428,61680,64764,65280],
  [170,43520,43690,52428,61680,65280,65450],
  [170,43520,43690,52428,61680,65280,65484],
  [170,43656,43690,52428,61680,65280,65484],
  [170,43690,49152,49344,52428,61680,65280],
  [170,43690,49152,52224,52428,61680,65280],
  [170,43690,49216,49344,52428,61680,65280],
  [170,43690,49216,52292,52428,61680,65280],
  [170,43690,49344,49386,52428,61680,65280],
  [170,43690,49344,52224,52428,61680,65280],
  [170,43690,49344,52292,52428,61680,65280],
  [170,43690,49344,52428,52462,61680,65280],
  [170,43690,49344,52428,60138,61680,65280],
  [170,43690,49344,52428,61166,61680,65280],
  [170,43690,49344,52428,61680,64764,65280],
  [170,43690,49344,52428,61680,65280,65450],
  [170,43690,49344,52428,61680,65280,65472],
  [170,43690,49344,52428,61680,65280,65484],
  [170,43690,49352,52428,61680,61690,65280],
  [170,43690,51400,52428,61680,64250,65280],
  [170,43690,52224,52292,52428,61680,65280],
  [170,43690,52224,52394,52428,61680,65280],
  [170,43690,52224,52428,52462,61680,65280],
  [170,43690,52224,52428,61098,61680,65280],
  [170,43690,52224,52428,61166,61680,65280],
  [170,43690,52224,52428,61440,61680,65280],
  [170,43690,52224,52428,61520,61680,65280],
  [170,43690,52224,52428,61680,61690,65280],
  [170,43690,52224,52428,61680,64250,65280],
  [170,43690,52224,52428,61680,64752,65280],
  [170,43690,52224,52428,61680,64764,65280],
  [170,43690,52224,52428,61680,65280,65450],
  [170,43690,52224,52428,61680,65280,65484],
  [170,43690,52224,52428,61680,65280,65520],
  [170,43690,52292,52428,52462,61680,65280],
  [170,43690,52292,52428,61166,61680,65280],
  [170,43690,52292,52428,61520,61680,65280],
  [170,43690,52292,52428,61680,61690,65280],
  [170,43690,52292,52428,61680,64250,65280],
  [170,43690,52292,52428,61680,64756,65280],
  [170,43690,52292,52428,61680,64764,65280],
  [170,43690,52292,52428,61680,65280,65348],
  [170,43690,52292,52428,61680,65280,65450],
  [170,43690,52292,52428,61680,65280,65484],
  [170,43690,52292,52428,61680,65280,65520],
  [170,43690,52360,52428,61680,65280,65450],
  [170,43690,52416,52428,61680,65280,65520],
  [170,43690,52428,52462,61166,61680,65280],
  [170,43690,52428,52462,61680,61690,65280],
  [170,43690,52428,52462,61680,64250,65280],
  [170,43690,52428,52462,61680,64764,65280],
  [170,43690,52428,52462,61680,64766,65280],
  [170,43690,52428,52462,61680,65280,65450],
  [170,43690,52428,52462,61680,65280,65484],
  [170,43690,52428,52462,61680,65280,65518],
  [170,43690,52428,52462,61680,65280,65520],
  [170,43690,52428,60928,61166,61680,65280],
  [170,43690,52428,60996,61166,61680,65280],
  [170,43690,52428,61166,61680,64250,65280],
  [170,43690,52428,61166,61680,64764,65280],
  [170,43690,52428,61166,61680,65278,65280],
  [170,43690,52428,61166,61680,65280,65450],
  [170,43690,52428,61166,61680,65280,65484],
  [170,43690,52428,61166,61680,65280,65518],
  [170,43690,52428,61166,61680,65280,65520],
  [170,43690,52428,61680,64512,64764,65280],
  [170,43690,52428,61680,64596,64764,65280],
  [170,43690,52428,61680,64764,64766,65280],
  [170,43690,52428,61680,64764,65278,65280],
  [170,43690,52428,61680,64764,65280,65450],
  [170,43690,52428,61680,64764,65280,65484],
  [170,43690,52428,61680,64764,65280,65532],
  [170,43690,52428,61680,65280,65348,65484],
  [170,43690,52428,61680,65280,65450,65484],
  [170,43690,52428,61680,65280,65450,65518],
  [170,43690,52428,61680,65280,65484,65518],
  [170,43690,52428,61680,65280,65484,65520],
  [170,43690,52428,61680,65280,65484,65532],
  [234,43690,49344,52428,60138,61680,65280],
  [238,3598,43690,52428,61166,61680,65280],
  [238,34952,43690,52428,61166,61680,65280],
  [238,41120,43690,52428,61166,61680,65280],
  [238,43520,43690,52428,61166,61680,65280],
  [238,43690,43758,52428,61166,61680,65280],
  [238,43690,52428,57568,61166,61680,65280],
  [238,43690,52428,60928,61166,61680,65280],
  [238,43690,52428,61166,61440,61680,65280],
  [238,43690,52428,61166,61456,61680,65280],
  [238,43690,52428,61166,61680,61694,65280],
  [238,43690,52428,61166,61680,64250,65280],
  [238,43690,52428,61166,61680,65278,65280],
  [238,43690,52428,61166,61680,65280,65450],
  [238,43690,52428,61166,61680,65280,65518],
  [238,43690,52428,61166,61680,65280,65520],
  [238,43690,52428,61680,65280,65450,65518],
  [254,43690,52428,61166,61680,65278,65280],
  [682,43690,52428,61680,64512,64764,65280],
  [2184,2730,43690,52428,61440,61680,65280],
  [2184,34952,43690,52428,61440,61680,65280],
  [2730,3276,43690,52428,61440,61680,65280],
  [2730,34952,43690,52428,61440,61680,65280],
  [2730,40960,41120,43690,52428,61680,65280],
  [2730,40960,43690,52428,61440,61680,65280],
  [2730,41120,43690,52428,61440,61680,65280],
  [2730,43690,49152,52428,61440,61680,65280],
  [2730,43690,49344,52428,61440,61680,65280],
  [2730,43690,50244,52428,61440,61680,65280],
  [2730,43690,52428,52974,61440,61680,65280],
  [2730,43690,52428,61166,61440,61680,65280],
  [2730,43690,52428,61440,61520,61680,65280],
  [2730,43690,52428,61440,61680,64170,65280],
  [2730,43690,52428,61440,61680,64250,65280],
  [2730,43690,52428,61440,61680,64716,65280],
  [2730,43690,52428,61440,61680,64764,65280],
  [2730,43690,52428,61440,61680,65280,65520],
  [2810,43690,52428,61440,61680,64250,65280],
  [3822,43690,52428,61166,61440,61680,65280],
  [4080,43690,52428,61440,61680,65280,65520],
  [10922,43690,49152,49344,52428,61680,65280],
  [32768,32896,34952,43690,52428,61680,65280],
  [32768,34952,43690,52428,61440,61680,65280],
  [32896,34816,34952,43690,52428,61680,65280],
  [32896,34952,41120,43690,52428,61680,65280],
  [32896,34952,43520,43690,52428,61680,65280],
  [32896,34952,43690,52428,61166,61680,65280],
  [32896,34952,43690,52428,61440,61680,65280],
  [32896,34952,43690,52428,61680,63736,65280],
  [32896,34952,43690,52428,61680,64250,65280],
  [32896,34952,43690,52428,61680,65280,65408],
  [32896,34952,43690,52428,61680,65280,65416],
  [32896,34952,43690,52428,61680,65280,65450],
  [32896,34952,43690,52428,61680,65280,65520],
  [34944,34952,43690,52428,61680,65280,65520],
  [34944,43680,43690,52428,61680,65280,65520],
  [34952,41120,43176,43690,52428,61680,65280],
  [34952,41120,43520,43690,52428,61680,65280],
  [34952,41120,43690,49344,52428,61680,65280],
  [34952,41120,43690,52224,52428,61680,65280],
  [34952,41120,43690,52428,60652,61680,65280],
  [34952,41120,43690,52428,61166,61680,65280],
  [34952,41120,43690,52428,61680,64764,65280],
  [34952,41120,43690,52428,61680,65280,65416],
  [34952,41120,43690,52428,61680,65280,65450],
  [34952,41120,43690,52428,61680,65280,65484],
  [34952,43176,43690,52428,61680,63736,65280],
  [34952,43176,43690,52428,61680,64764,65280],
  [34952,43680,43690,52428,61680,65280,65520],
  [34952,43690,52428,57568,61166,61680,65280],
  [34952,43690,52428,61166,61440,61680,65280],
  [34952,43690,52428,61166,61680,63736,65280],
  [34952,43690,52428,61166,61680,64250,65280],
  [34952,43690,52428,61166,61680,65278,65280],
  [34952,43690,52428,61166,61680,65280,65520],
  [34952,43690,52428,61440,61680,63624,65280],
  [34952,43690,52428,61440,61680,63736,65280],
  [34952,43690,52428,61440,61680,64250,65280],
  [34952,43690,52428,61568,61680,65280,65416],
  [34952,43690,52428,61600,61680,65280,65450],
  [34952,43690,52428,61680,63736,64250,65280],
  [34952,43690,52428,61680,63736,65280,65416],
  [34952,43690,52428,61680,63736,65280,65450],
  [34952,43690,52428,61680,63736,65280,65520],
  [34952,43690,52428,61680,63736,65280,65528],
  [34952,43690,52428,61680,64250,64764,65280],
  [34952,43690,52428,61680,64250,65278,65280],
  [34952,43690,52428,61680,64250,65280,65450],
  [34952,43690,52428,61680,64250,65280,65484],
  [34952,43690,52428,61680,64250,65280,65520],
  [34952,43690,52428,61680,64250,65280,65530],
  [34952,43690,52428,61680,65280,65520,65528],
  [34952,43690,52428,61680,65280,65520,65530],
  [43176,43690,52428,60652,61680,64764,65280],
  [43176,43690,52428,61166,61680,64764,65280],
  [43176,43690,52428,61680,64512,64764,65280],
  [43176,43690,52428,61680,64764,65278,65280],
  [43176,43690,52428,61680,64764,65280,65448],
  [43176,43690,52428,61680,64764,65280,65450],
  [43176,43690,52428,61680,64764,65280,65484],
  [43176,43690,52428,61680,64764,65280,65532],
  [43688,43690,52428,61680,64764,65280,65532],
  [43690,52428,60138,61166,61680,64250,65280],
  [43690,52428,61152,61166,61680,65280,65520],
  [43690,52428,61166,61680,64250,64764,65280],
  [43690,52428,61166,61680,64250,65278,65280],
  [43690,52428,61166,61680,64250,65280,65450],
  [43690,52428,61166,61680,64250,65280,65484],
  [43690,52428,61166,61680,64250,65280,65518],
  [43690,52428,61166,61680,65278,65280,65518],
  [43690,52428,61166,61680,65278,65280,65520],
  [43690,52428,61166,61680,65278,65280,65534],
  [43690,52428,61166,61680,65280,65520,65534]]
def permDigits : List Nat := [18364758544493064720,18364683486789906960,18355225778678027280,18336085189344794640,18355113192123290640,18336047660493215760,18297203519274627360,18297128461571469600,18152560703022715200,17863200012815733120,18152448116467978560,17863162483964154240,18282904370552071200,18263763781218838560,18147794320115196480,17858433629908214400,18119083436115347520,17848863335241598080,18282773019571545120,18263707487941470240,18147662969134670400,17858377336630846080,18119064671689558080,17848844570815808640]
def moves : List (List Nat) := [
  [0,65706,201392332,268501232,33622538,234949644,302059264,134292002,335622192,369177344,604062788,671174736,704730368,166024,67281056,100837888,43690,402833600,436390912,52428,257774,537063424,61680,67369722,402914556,65280,100925354,436469708,537133040],
  [65536,262154,67371042,393352,67502240,65706,524492,67633392,592394,658444,724736,67707426,67776560,67842816,604718148,671830096,808192,886920,68001952,961024,109226,1032384,1100800,1166404,117964,1232110,1306350,68218880,68284496,127216,68350202,68418298,1375484,130816,1441706,1507276,68616176],
  [131072,458888,852138,202178764,269418736,34015240,34408970,235736076,302976768,135143970,336605232,370160384,604914756,672157776,705713408,538472560,572028672,1671296,35227648,166024,1745056,35301888,174762,203079872,236637184,183500,1830638,1896448,192752,1964280,2030330,203357436,196352,35520392,35585962,236912588,2097136],
  [196608,1245354,202571980,1507566,269746416,34802186,236129292,35065358,303304448,537202704,570757376,135602722,336998448,370553600,605373508,672550992,706106624,1804424,69116064,102672896,240298,404668608,438225920,249036,270590176,304147968,257774,538963968,258288,2226938,203554044,2293502,261888,35782570,237109196,35848174,2359280],
  [262144,2359298,2621448,262154,3080226,3145864,3211424,262314,3277004,3342576,3410442,3476492,3542784,3613218,3682352,3748608,3818564,3887184,3953920,4032648,4104352,4172288,4237984,305834,4309184,4377600,4443204,4508868,314572,4574414,4639982,4714222,4780032,4845648,323824,4911354,4979450,5045500,327424,5111562,5177258,5242828,5308400],
  [327680,2424834,2686984,327690,3014668,5243050,5308620,5439728,38799882,38865932,38997760,5579298,5648432,39203584,5714736,5784644,5853264,39408896,5920080,5998728,6135968,39692800,6204064,371370,6275264,39832576,6343872,6409412,380108,6474958,6549230,6615040,389360,6680826,6748922,6814972,392960,40238858,40304554,40370124,393200,6881274,6946812],
  [393216,2752520,3145738,70320162,7274624,393352,7536800,393386,7602380,7667952,7735818,7801868,7868160,7938594,8007728,8073984,8143940,8212560,8279296,8358024,8429728,8497664,8563234,436906,8634560,8702976,8768580,445644,8834286,8908526,8974336,9039952,9105520,454896,9171192,9236730,9304826,9370876,458496,9437064,9502634,9568204,9633776],
  [458752,2818056,7340160,458888,8323242,209649868,9634032,9701384,9767434,211094540,9834240,9904674,10104880,10171136,211240004,211439696,211506432,10252400,10319616,10387584,10455040,493704,10526880,10594816,10660386,502442,211861696,211930112,211995716,511180,10743534,10809344,10874992,520432,10940664,11008248,11074298,212401404,524032,11141000,11206570,212533196,11272176],
  [524288,3276810,204603404,70451234,405995588,7602312,74776736,524458,410321088,524492,11731182,11796720,11864586,213191692,11931392,12001826,12070960,12137216,213337156,213405776,213472512,12224648,12296352,12364288,12429858,567978,12495598,213631168,213699584,213765188,576716,213830894,12578542,12644352,12709936,214036560,585968,12775674,214102268,12843770,214170876,589568,12910506,214237132,12976112],
  [589824,3407882,70713378,7733384,75038880,589994,11862220,79102192,104268290,41289736,108595712,592394,13175466,45419532,112660224,13247010,13316144,46871296,13386820,13455440,47011072,13535368,13607072,47163904,633514,13680832,13747396,47238144,47303748,642252,13815022,47369934,13889262,13955072,14020688,651504,14086394,47576320,14154490,14220540,655104,47644426,47710122,47775692,14286832],
  [655360,2883592,3473418,238354444,70778914,7798920,75104416,78446754,655530,213188812,79167728,439878660,242681864,45419018,444206080,447548420,658444,14421166,448270080,80421410,14495792,14562048,449528900,249450576,249386240,14649480,14721184,14787234,14854656,699050,14921390,249741504,249613312,249678916,707788,249810158,15003374,15069184,15134800,717040,15200506,250016512,15268602,15334652,720640,250085132,250216362,250150860,15400944],
  [720896,3538954,70844450,7864456,75169952,721066,11927756,79233264,305791744,507184384,310118912,112658954,511511552,448269324,724736,15667114,147530274,81670192,315372288,652100676,15749200,516773120,15829128,15900832,15966378,16034304,764586,16101290,16171200,16236748,16305152,16370756,773324,16436462,16502732,16576238,16642048,16707664,782576,16773370,16841466,16907516,786176,16973738,17039308,17104880],
  [786432,3932170,71041058,8257672,75366560,786602,213450956,280559856,708576512,46991882,249367564,516755200,775688448,147661346,350040112,583873280,712918016,649675844,780029952,750342224,808192,17585578,17664136,17729740,84779168,84844784,17803776,830122,17875136,722324480,722390084,838860,17943790,722591180,18018030,789442560,789508176,848112,85061882,789706224,85129978,18087164,851712,18153386,722665420,789774320],
  [851968,3997706,71172130,8323208,75497632,852138,12189900,79364336,43321352,13502986,14617612,15798016,80683554,81801264,82981632,619988036,687362128,17650944,84570224,85358336,18317440,18450432,886920,18712746,18784416,18852352,895658,18923712,18992128,19057732,904396,19123438,19197678,19263488,19329104,913648,19394810,19462392,19528442,19594492,917248,19660680,19726250,19791820,19857392],
  [917504,4128778,71237666,8454280,75563168,917674,12320972,79429872,110561792,47122954,14814220,15994624,177676800,147792418,81932336,83112704,620577860,17384652,687689808,84496624,17782016,18515968,18843784,85630976,85958816,961024,961194,20037824,20106240,20171844,969932,20237550,20311756,20377326,87224320,87289936,979184,87355642,87423728,87489274,20446460,982784,20512682,20578252,87687152],
  [983040,4259850,71368738,7077930,7405696,8585352,75694240,983210,412287168,213582028,280690928,13634058,249695244,16125696,80749090,17246762,350367792,83243776,17317632,613826624,619791428,686903376,17847552,18382976,18909320,86024352,20032000,1026730,20692992,20824128,1032384,20955370,21023744,21089348,1035468,21155054,21228266,21294830,88141824,88207440,1044720,88273146,88406778,21363964,1048320,21430186,21495744,21561292,88670192],
  [1048576,4325386,71827490,8650888,76021920,1048746,213647564,79692016,47188490,446303232,249564172,16256768,81011234,81404586,82128944,82653424,83702528,647709696,619856964,687231056,722294016,18581504,18974856,86352032,20097536,1092266,20758528,21020864,1100800,21744708,21810346,1101004,21875950,21950122,22015726,22081536,22147152,1110256,22212858,22280954,22346992,22412540,1113856,22478762,22544332,22609904],
  [1114112,4390922,71893026,408027204,8716424,76087456,1114282,213713100,281084144,47254026,447613956,249629708,16322304,81076770,81470122,82194480,82587824,83768064,619922500,687296592,722359552,18647040,19040392,86417568,20163072,1157802,20889664,21086400,21744640,1166404,1166540,22662382,22736622,89255936,22802512,1175792,22868218,22936314,23002356,23067900,1179392,23134020,23199658,23265228,23330800],
  [1179648,4587530,71958562,8781960,76284064,1179818,213778636,12976366,79823088,13765130,249760780,15404046,16387840,177742336,81142306,548352016,82260016,83833600,620053572,687558736,17913088,19105928,19892394,86483104,20228608,1223338,21151936,88719584,21875712,22662212,1232076,1232110,23523054,89321472,89976912,1241328,23589114,23657210,23723260,23788798,1244928,23855018,23920588,23986158,24051696],
  [1245184,4653066,72024098,8847496,76349600,1245354,12517580,13041902,79888624,13830666,14945292,15601166,16518912,542511120,576262400,81207842,82325552,83899136,620905540,688083024,17978624,19171464,86614176,20359680,1288874,21283008,22006784,22727748,1297612,23514350,88793312,24112640,24178244,1306350,89387008,90042448,1306864,90763514,24247034,24313084,24379134,1310464,24444842,24510412,24575982,24641520],
  [1310720,2490370,4980746,72089634,9306248,76415136,11534504,1310890,214106316,281215216,13107452,106234370,307757824,14158346,15272972,16846592,81273378,82391088,83964672,620512324,687624272,17519700,18044160,19564680,86679712,19966120,20425216,1354410,21348544,22400000,23055428,1363148,23710958,24309486,89518080,90173520,1372400,90829050,91421434,24706048,24771668,1375484,24837374,24903422,1376000,24969130,25034700,92143600,25100284],
  [1376256,5111818,72220706,408092740,475201616,9437320,76546208,1376426,12845260,79954160,47647242,250153996,16912128,17108746,148316706,350826544,84030208,84226850,621036612,688148560,18109696,19695752,86810784,20490752,1419946,21414080,22465536,23186500,23383176,1428684,23842030,24440558,89583616,90304592,90501280,1437936,90960122,91552506,24968444,1441536,1441706,25231308,25296878,92340208,92405754],
  [1441792,5177354,72351778,273743920,9502856,76677280,1441962,214171852,80019696,47712778,250088460,16977664,17174284,81338914,82456624,84161280,620774468,687951952,722621696,18175300,19761288,86941856,20556288,20621960,1485482,21545152,22531072,23252036,1494220,23907566,24506094,89714688,90435664,90566848,1503472,91156730,91749114,25033980,1507072,25165636,25231274,1507276,25362414,25427952,25493500],
  [1507328,6946830,72613922,408158276,13041834,214368460,280035552,1507566,281542896,49154570,250481676,25562638,319491840,542576656,576327936,151331362,352727088,387265280,621102148,688279632,722818304,25659528,25731232,25799168,1551018,25864942,227066048,227134464,1559756,227200238,25944288,26013184,1568494,26079232,26144784,1569008,26210558,26278650,227605756,26345214,1572608,26410922,227737548,26476526,26542064],
  [1572864,77136032,14287018,216858828,285802736,141361698,26740872,110692864,47843850,1575594,250416140,26873036,319360768,151462434,547106816,352989232,386544384,621298756,748507136,689328208,722883840,26970248,27107328,27173024,60729856,1616554,27246592,27312320,27378756,60869632,1625292,27447022,27520750,1634304,27586640,1634544,61142272,27654826,27720442,27786444,27852028,1638144,61276074,61407180,27918320],
  [1638400,7471232,10354824,18284714,219611340,286785776,43976712,51972618,253299724,322637568,152707618,127674922,354103344,389821184,622478404,463227980,689655888,725374208,563966064,597653248,330137344,28213248,1671296,28346368,1673352,28418208,28486144,1682090,229753024,229821440,1690828,28569326,28635136,1700080,28702968,28769018,230096124,1703680,28835712,28901256,28966826,230293452,29032432],
  [1703936,10485896,77594784,18743466,220201164,287310064,44107784,52365834,253824012,322965248,144777248,153035298,354496560,390083328,624051268,463359052,691163216,726684928,530603776,564031600,597718784,28409984,62031872,1738888,162701312,1745056,29206696,29272576,1747626,29343936,29412352,1756364,29486316,29552366,96530432,1765616,96598264,96664314,29621500,1769216,29687688,96796576,29753258,29818828,96927728],
  [1769472,10682504,19136682,220463308,25624814,289734896,44238856,52693514,254020620,59182606,323292928,543428624,576983296,154673698,358035504,391590656,624444484,693588048,727143680,564946534,564752496,598308608,28541056,62097408,1804424,29532320,63089152,1813162,230867136,264424448,1821900,30073056,63630848,1830638,30142464,1831152,30210296,30276346,231603452,30342910,1834752,63766408,63831978,265158604,63897582,30408688],
  [1835008,10748040,19202218,220528844,288424176,44304392,26806408,52759050,26938026,254086156,228265164,321982208,154214946,547631104,556085296,589640448,623985732,748965888,757420112,790975744,563703808,563834992,597391104,28278784,28606592,62162944,1869960,565485568,96510112,130066944,1878698,766820352,432062656,465619968,1887436,30142190,1896448,1896688,30472328,30537976,567409322,30604026,768736460,231931132,1900288,64094088,64159658,265486284,567017456],
  [1900544,10944648,19398826,220725452,289603824,293929208,106693122,442237956,309200640,44632072,53152266,254479372,323424000,154477090,357445680,391394048,624247876,692998224,726947072,564490352,598177536,28672128,62425088,1935496,96575648,29862056,63220224,1944234,432128192,231196872,264555520,1952972,30207726,30535680,1962224,64223232,1964280,30800634,232127740,1965824,30867336,30932906,232259532,30998512,31064056],
  [1966080,11010184,19464362,220856524,289669360,92799226,442303492,509543680,44697608,53217802,254610444,323489536,154542626,357511216,159986226,391459584,624510020,693522512,727209216,564555888,564818546,598243072,28737664,62490624,2001032,96641184,63285760,2009770,230932672,231262408,264686592,2018508,30273262,30601216,2027760,30800120,64289280,2030330,31128828,31194878,2031360,64487304,31260586,31326156,31391728,31457274],
  [2031616,2949128,5963786,207290380,11206792,19792042,221118668,289800432,44763144,53348874,254675980,323358464,154608162,357773360,391328512,562901808,624378948,693325904,726881536,764237136,564359280,597915392,564885360,28999808,62556160,29067392,2066568,96903328,130460160,29993632,2075306,432455872,466013184,231328960,2084044,30404334,567013376,2093296,30996728,31390458,232717564,2096896,64552840,64946090,266272716,2097136,31522808,31588346,232914940],
  [2097152,11665576,19923114,222953676,290062576,428540156,106824194,308282112,44828680,54135306,258214924,325390080,145498144,154804770,358887472,392508160,628048964,695160912,629953620,729306368,731338496,29919368,97034400,129804288,2140328,130656768,2140842,432718016,466930688,2149580,31649004,31715054,567603200,2158832,98760952,98827002,31783936,2161916,31850238,2162432,31915944,31981482,32047052,99155952,32112636],
  [2162688,24182954,225575116,26214638,292684016,93323514,442893316,510067968,57936394,259329036,59903502,326962944,543559696,577179904,158605858,360001584,160576050,394081024,629163076,696275024,730027264,30247048,97362080,131901952,2206378,433766592,233031880,467586048,2215116,300146912,32238314,334032384,2223854,568258560,2224368,401144320,2226938,32374012,32440062,2227968,32505770,32571340,32636910,99680240,99745786],
  [2228224,24314026,225640652,26280174,293273840,26607870,304546048,58067466,259394572,59969038,327028480,543690768,577310976,159457826,360853552,160772658,394539776,629228612,696406096,630543444,730092800,30312584,98279584,132098560,2271914,433832128,467651584,2280652,300277984,334097920,2289390,568455168,2289904,32439034,233766140,334167552,2293502,2293504,66191274,267517900,32702446,32767984,32833534],
  [2293760,6488074,207814668,7012366,24576170,225902796,26476782,293339376,58133002,259460108,60034574,326897408,543363088,576917760,543887632,159130146,561459248,595014400,563360560,628900932,762794064,796349696,764695888,30378120,98410656,131967488,166177440,2337450,433963200,467520512,635948224,2346188,300409056,333966848,32304864,2354926,567275520,2355440,99678970,435223804,32767742,2359040,133234602,468778956,66322414,2359280,569638906,770965500,32899070]]
def state (i : Nat) : List T := stages3.getD i []
def perm (j : Nat) (i : Fin 16) : Fin 16 :=
  ⟨((permDigits.getD j 0) >>> (4*i.val)) % 16, Nat.mod_lt _ (by decide)⟩
def word (m : Nat) : T := BitVec.ofNat 16 m
def dest (m : Nat) := (m/65536)%512
def movePerm (m : Nat) := perm (m/33554432)
def limit (i : Nat) := if i<1 then 4 else if i<4 then 36 else 502

def works (s : List T) (n m : Nat) : Bool :=
  decide (dest m<n) && (ren (movePerm m) tgt == tgt) &&
  (sat (word m::s)).all (fun x=>decide (ren (movePerm m) x ∈ sat (state (dest m))))
def norm (g : T) := if g[0] then neg g else g

def cert (i : Nat) : Bool :=
  let ms := moves.getD i []
  ms.all (works (state i) (limit i)) &&
  (combs (state i)).all (fun g=>ms.any (fun m=>word m == norm g))

theorem enclose {s : List T} {g : T} : ∀ x∈sat (g::s), x∈sat (norm g::s) := by
  intro x hx
  by_cases e : g[0]=true
  · rw [norm,ite_eq_left e]
    rcases K4Core.ext hx with h|eq|eq
    · exact src (fun t ht=>List.mem_cons_of_mem _ ht) h
    · rw [eq]
      have hh := negmem (x:=neg g) (s:=neg g::s) (by simp [sat])
      simpa [neg] using hh
    · simp [eq,sat]
  · simpa [norm,e] using hx

theorem follow {k i} (hc : cert i=true) (hr : Reach (k+1) (state i) tgt) :
    ∃ j, j<limit i ∧ Reach k (state j) tgt := by
  simp only [cert,Bool.and_eq_true,List.all_eq_true] at hc
  cases hr with | @step _ s g z hg tail =>
    obtain ⟨m,member,hm⟩ := List.any_eq_true.mp (hc.2 g hg)
    have good := hc.1 m member
    simp only [works,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,List.all_eq_true] at good
    have eq : word m=norm g := beq_iff_eq.mp hm
    have h := transfer (π:=movePerm m) (t:=state (dest m)) (by
      intro x hx
      apply good.2 x
      rw [eq]
      exact enclose x hx) tail
    exact ⟨dest m,good.1.1,good.1.2 ▸ h⟩


set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check0 : cert 0=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check1 : cert 1=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check2 : cert 2=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check3 : cert 3=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check4 : cert 4=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check5 : cert 5=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check6 : cert 6=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check7 : cert 7=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check8 : cert 8=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check9 : cert 9=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check10 : cert 10=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check11 : cert 11=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check12 : cert 12=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check13 : cert 13=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check14 : cert 14=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check15 : cert 15=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check16 : cert 16=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check17 : cert 17=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check18 : cert 18=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check19 : cert 19=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check20 : cert 20=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check21 : cert 21=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check22 : cert 22=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check23 : cert 23=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check24 : cert 24=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check25 : cert 25=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check26 : cert 26=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check27 : cert 27=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check28 : cert 28=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check29 : cert 29=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check30 : cert 30=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check31 : cert 31=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check32 : cert 32=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check33 : cert 33=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check34 : cert 34=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem check35 : cert 35=true := by decide +kernel
theorem checked (i : Fin 36) : cert i.val=true := by
  fin_cases i
  · exact check0
  · exact check1
  · exact check2
  · exact check3
  · exact check4
  · exact check5
  · exact check6
  · exact check7
  · exact check8
  · exact check9
  · exact check10
  · exact check11
  · exact check12
  · exact check13
  · exact check14
  · exact check15
  · exact check16
  · exact check17
  · exact check18
  · exact check19
  · exact check20
  · exact check21
  · exact check22
  · exact check23
  · exact check24
  · exact check25
  · exact check26
  · exact check27
  · exact check28
  · exact check29
  · exact check30
  · exact check31
  · exact check32
  · exact check33
  · exact check34
  · exact check35
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem orbitLower (last : ∀s∈stages3,¬Reach 3 s tgt) :
    ¬ Reach 6 [43690,52428,61680,65280] tgt := by
  intro h
  change Reach 6 (state 0) tgt at h
  obtain ⟨j,hj,r⟩ := follow check0 h
  change j<4 at hj
  obtain ⟨v,hv,q⟩ := follow (checked ⟨j,by omega⟩) r
  have v36 : v<36 := by simp [limit,hj] at hv;split_ifs at hv <;> omega
  obtain ⟨u,hu,e⟩ := follow (checked ⟨v,v36⟩) q
  have u502 : u<502 := by unfold limit at hu;split_ifs at hu <;> omega
  have um : u<stages3.length := by change u<502;exact u502
  have mem : state u ∈ stages3 := by rw [state,List.getD_eq_getElem _ _ um];exact List.getElem_mem _
  exact last (state u) mem e
end K4Orbit

namespace GuardDep
open K4Core
def Dep (u a b c : T) := ∀ i j:Fin 16, a[i.val]=a[j.val] → b[i.val]=b[j.val] →
  (c)[i.val]=(c)[j.val] → u[i.val]=u[j.val]

theorem dep_neg {u a b c} (h:Dep u a b c) : Dep (neg u) a b c := by
  intro i j x y z
  simp [neg,h i j x y z]

theorem dep0 {s:List T} {g z:T} (hg:g∈combs s) (hz:z∈sat (g::s)) :
    ∃a∈sat s,∃b∈sat s, ∀i j:Fin 16, a[i.val]=a[j.val] → b[i.val]=b[j.val] → z[i.val]=z[j.val] := by
  rcases K4Core.ext hz with h|rfl|rfl
  · exact ⟨z,h,z,h,fun _ _ x _ => x⟩
  all_goals
    obtain ⟨a,ha,w⟩ := List.mem_flatMap.mp hg
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp w
    refine ⟨a,ha,b,hb,?_⟩
    intro i j hi hj
    simp [neg,hi,hj]

theorem dep2 {s:List T} {z:T} (r:Reach 2 s z) :
    ∃a∈sat s,∃b∈sat s,∃c∈sat s, Dep z a b c := by
  cases r with | @step _ _ g _ hg r =>
    cases r with | @step _ _ h _ hh r =>
      cases r with | done hz =>
        rcases K4Core.ext hz with old|rfl|rfl
        · obtain ⟨a,ha,b,hb,q⟩ := dep0 hg old
          exact ⟨a,ha,b,hb,b,hb,fun i j x y _=>q i j x y⟩
        all_goals
          obtain ⟨x,hx,w⟩ := List.mem_flatMap.mp hh
          obtain ⟨y,hy,rfl⟩ := List.mem_map.mp w
          obtain ⟨a,ha,z,hz,e⟩ := fac hx hy
          obtain ⟨b,hb,c,hc,q⟩ := dep0 hg hz
          refine ⟨a,ha,b,hb,c,hc,?_⟩
          rw [e]
          intro i j x y w
          simp [neg,x,q i j y w]

def E (x t:T) := ∀ i j:Fin 16, t[i.val]=t[j.val] → x[i.val]=x[j.val]
theorem reflE (x:T) : E x x := fun _ _ h=>h
theorem negE (x:T) : E (neg x) x := by
  intro i j h; simp [neg,h]
theorem oldOr {s:List T} {g x:T} (h:x∈sat (g::s)) : x∈sat s ∨ E x g := by
  rcases K4Core.ext h with old|rfl|rfl
  · exact Or.inl old
  · exact Or.inr (reflE _)
  · exact Or.inr (negE _)

theorem dep3 {s:List T} {z:T} (r:Reach 3 s z) :
    ∃a∈sat s,∃b∈sat s,∃g∈combs s,Dep z a b g := by
  cases r with | @step _ _ g _ hg r =>
    obtain ⟨a,ha,b,hb,c,hc,d⟩ := dep2 r
    have hz : (0:T)∈sat s := by simp [sat]
    rcases oldOr ha with ap|ae <;> rcases oldOr hb with bp|be <;> rcases oldOr hc with cp|ce
    · have gg : c∈combs s := by simpa using meetmem cp cp
      exact ⟨a,ap,b,bp,c,gg,d⟩
    · exact ⟨a,ap,b,bp,g,hg,fun i j x y w=>d i j x y (ce i j w)⟩
    · exact ⟨a,ap,c,cp,g,hg,fun i j x y w=>d i j x (be i j w) y⟩
    · exact ⟨a,ap,a,ap,g,hg,fun i j x _ w=>d i j x (be i j w) (ce i j w)⟩
    · exact ⟨b,bp,c,cp,g,hg,fun i j x y w=>d i j (ae i j w) x y⟩
    · exact ⟨b,bp,b,bp,g,hg,fun i j x _ w=>d i j (ae i j w) x (ce i j w)⟩
    · exact ⟨c,cp,c,cp,g,hg,fun i j x _ w=>d i j (ae i j w) (be i j w) x⟩
    · exact ⟨0,hz,0,hz,g,hg,fun i j _ _ w=>d i j (ae i j w) (be i j w) (ce i j w)⟩
end GuardDep

namespace GuardDep
open K4Core
def marks (w:List T) (f:T→Bool) : Nat := w.foldr (fun u t=>t*2+(f u).toNat) 0
theorem markGet (w:List T) (f:T→Bool) (i:Nat) (hi:i<w.length) :
    (marks w f).testBit i=f w[i] := by
  induction w generalizing i with
  | nil => simp at hi
  | cons a l ih =>
    cases i with
    | zero =>
      simp only [marks,List.foldr_cons,List.getElem_cons_zero]
      cases e:f a <;> simp [e,Nat.testBit_zero]
    | succ i =>
      change ((marks l f)*2+(f a).toNat).testBit (i+1) = _
      rw [Nat.testBit_succ]
      have d : ((marks l f)*2+(f a).toNat)/2=marks l f := by cases f a <;> simp <;> omega
      rw [d]
      exact ih i (by simpa using hi)
abbrev ERow := Fin 16 × Fin 16 × Nat
def edges (ws:List T) : List ERow :=
  let rows := (List.finRange 16).map (fun i=>(i,marks ws (fun x=>x[i.val])))
  rows.flatMap fun a=>rows.filterMap fun b=>
    if a.1.val < b.1.val then some (a.1,b.1,a.2^^^b.2) else none
theorem edgeSound {ws:List T} {e:ERow} (he:e∈edges ws) (u:Nat) (hu:u<ws.length) :
    e.2.2.testBit u = (ws[u][e.1.val] != ws[u][e.2.1.val]) := by
  obtain ⟨a,ha,rest⟩ := List.mem_flatMap.mp he
  obtain ⟨b,hb,hbval⟩ := List.mem_filterMap.mp rest
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hb
  split at hbval <;> simp_all only [Option.some.injEq,reduceCtorEq]
  subst e
  simp [Nat.testBit_xor,markGet,hu]
def agree (x:T) (e:ERow) := x[e.1.val] == x[e.2.1.val]
def trim (b:T) : List ERow→ Nat→Bool
  | [],k => k != 0
  | e::es,k => if k=0 then false else trim b es (if agree b e then k &&& e.2.2 else k)
theorem trimKeep {b:T} (es:List ERow) {u k:Nat} (hk:k.testBit u=true)
    (surv:∀e∈es,agree b e=true → e.2.2.testBit u=true) : trim b es k=true := by
  induction es generalizing k with
  | nil =>
    have ne : k≠0 := by intro h; simp [h] at hk
    simp [trim,ne]
  | cons e l ih =>
    have ne : k≠0 := by intro h; simp [h] at hk
    rw [trim,ite_eq_right_iff.mpr (fun h=>(ne h).elim)]
    apply ih
    · split <;> rename_i h
      · simp [Nat.testBit_and,hk,surv e (List.mem_cons_self ..) h]
      · exact hk
    · exact fun x hx=>surv x (List.mem_cons_of_mem _ hx)

def quick (s:List T) (t:T) : Bool :=
  let ws := combs s
  let initial := marks ws (fun _=>true)
  let es := (edges ws).filter fun e=>!(agree t e)
  let old := 0::s
  old.any fun a=>
    let left := es.filter (agree a)
    old.any fun b=>trim b left initial
theorem representative {s:List T} {x:T} (h:x∈sat s) : ∃a∈0::s,E x a := by
  simp only [sat,List.mem_cons,List.mem_append,List.mem_map] at h
  rcases h with rfl|rfl|p|⟨y,hy,rfl⟩
  · exact ⟨0,List.mem_cons_self ..,reflE _⟩
  · exact ⟨0,List.mem_cons_self ..,negE 0⟩
  · exact ⟨_,List.mem_cons_of_mem _ p,reflE _⟩
  · exact ⟨_,List.mem_cons_of_mem _ hy,negE _⟩
theorem quickOf {s:List T} {t:T} (h:Reach 3 s t) : quick s t=true := by
  obtain ⟨a,ha,b,hb,c,hc,dep⟩ := dep3 h
  obtain ⟨u,hu,ua⟩ := representative ha
  obtain ⟨v,hv,vb⟩ := representative hb
  obtain ⟨idx,ib,eq⟩ := List.mem_iff_getElem.mp hc
  unfold quick
  refine List.any_eq_true.mpr ⟨u,hu,List.any_eq_true.mpr ⟨v,hv,?_⟩⟩
  apply trimKeep (u:=idx) _ (markGet _ (fun _=>true) idx ib)
  intro e he ve
  have el := List.mem_filter.mp he
  have info := List.mem_filter.mp el.1
  rw [edgeSound info.1 _ ib,eq]
  by_contra! no
  have ec : (c)[e.1.val]=(c)[e.2.1.val] := by simpa using no
  have same := dep _ _ (ua _ _ (beq_iff_eq.mp el.2)) (vb _ _ (beq_iff_eq.mp ve)) ec
  simpa [agree,same] using info.2
end GuardDep

namespace GuardPair
open K4Core
def finishAt (s:List T) (t:T) := (combs s).any fun g => two (g::s) t (neg t)
theorem fromTail {s : List T} {z:T} (hr:Reach 3 s z) : finishAt s z=true := by
  cases hr with | step hg h1 =>
    cases h1 with | step hh h2 =>
      cases h2 with | step hi h3 =>
        cases h3 with | done hz =>
          have hfit : fits z z (K4Core.neg z)=true := by simp [fits,K4Core.neg,BitVec.and_comm]
          exact List.any_eq_true.mpr ⟨_,hg,two_all hh hi hz hfit⟩
end GuardPair

namespace GuardDep
open K4Core
open GuardPair (finishAt fromTail)
def shrink (b:T) : List ERow→Nat→Nat
  | [],k => k
  | e::es,k => if k=0 then 0 else shrink b es (if agree b e then k &&& e.2.2 else k)
theorem keepBit {b:T} (es:List ERow) {u k:Nat} (hk:k.testBit u=true)
    (surv:∀e∈es,agree b e=true → e.2.2.testBit u=true) : (shrink b es k).testBit u=true := by
  induction es generalizing k with
  | nil => exact hk
  | cons e l ih =>
    have ne : k≠0 := by intro h;simp [h] at hk
    rw [shrink,ite_eq_right_iff.mpr (fun h=>(ne h).elim)]
    apply ih
    · split <;> rename_i h
      · simp [Nat.testBit_and,hk,surv e (List.mem_cons_self ..) h]
      · exact hk
    · exact fun x hx=>surv x (List.mem_cons_of_mem _ hx)

def joined {α} (l:List α) (f:α→Nat) := l.foldr (fun x a=>f x ||| a) 0
theorem joinedBit {α} (l:List α) (f:α→Nat) {u} {x:α} (hx:x∈l) (h:(f x).testBit u=true) :
    (joined l f).testBit u=true := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    change (f a ||| joined l f).testBit u=true
    rw [Nat.testBit_or]
    rcases List.mem_cons.mp hx with rfl|old
    · simp [h]
    · simp [ih old]

def candidates (s:List T) (t:T) : Nat :=
  let ws := combs s
  let initial := marks ws (fun _=>true)
  let es := (edges ws).filter fun e=>!(agree t e)
  let old := 0::s
  joined old fun a=>
    let left := es.filter (agree a)
    joined old fun b=>shrink b left initial

theorem selected {s:List T} {a b t:T} {idx:Nat} (ib:idx<(combs s).length)
    (ha:a∈sat s) (hb:b∈sat s) (dep:Dep t a b (combs s)[idx]) : (candidates s t).testBit idx=true := by
  obtain ⟨u,hu,ua⟩ := representative ha
  obtain ⟨v,hv,vb⟩ := representative hb
  unfold candidates
  apply joinedBit _ _ hu
  apply joinedBit _ _ hv
  apply keepBit _ (markGet _ (fun _=>true) idx ib)
  intro e he ve
  have el := List.mem_filter.mp he
  have info := List.mem_filter.mp el.1
  rw [edgeSound info.1 _ ib]
  by_contra! no
  have ec : (combs s)[idx][e.1.val]=(combs s)[idx][e.2.1.val] := by simpa using no
  have same := dep _ _ (ua _ _ (beq_iff_eq.mp el.2)) (vb _ _ (beq_iff_eq.mp ve)) ec
  simpa [agree,same] using info.2

def usable (s:List T) (t:T) : List T :=
  let kept := candidates s t
  ((combs s).zipIdx.filter (fun gi=>kept.testBit gi.2)).map Prod.fst
theorem usableOf {s:List T} {a b c t:T} (ha:a∈sat s) (hb:b∈sat s) (hc:c∈combs s)
    (dep:Dep t a b c) : c∈usable s t := by
  obtain ⟨i,ib,eq⟩ := List.mem_iff_getElem.mp hc
  apply List.mem_map.mpr ⟨(c,i),?_,rfl⟩
  apply List.mem_filter.mpr
  constructor
  · apply List.mk_mem_zipIdx_iff_getElem?.mpr
    rw [List.getElem?_eq_getElem ib,eq]
  · apply selected ib ha hb
    rw [eq];exact dep

theorem separateGate {s:List T} {g t:T} (r:Reach 2 (g::s) t) :
   (∃a∈sat s,∃b∈sat s,∃c∈sat s,Dep t a b c) ∨ (∃a∈sat s,∃b∈sat s,Dep t a b g) := by
  obtain ⟨a,ha,b,hb,c,hc,d⟩ := dep2 r
  have hz : (0:T)∈sat s := by simp [sat]
  rcases oldOr ha with ap|ae <;> rcases oldOr hb with bp|be <;> rcases oldOr hc with cp|ce
  · exact Or.inl ⟨a,ap,b,bp,c,cp,d⟩
  · exact Or.inr ⟨a,ap,b,bp,fun i j x y w=>d i j x y (ce i j w)⟩
  · exact Or.inr ⟨a,ap,c,cp,fun i j x y w=>d i j x (be i j w) y⟩
  · exact Or.inr ⟨a,ap,a,ap,fun i j x _ w=>d i j x (be i j w) (ce i j w)⟩
  · exact Or.inr ⟨b,bp,c,cp,fun i j x y w=>d i j (ae i j w) x y⟩
  · exact Or.inr ⟨b,bp,b,bp,fun i j x _ w=>d i j (ae i j w) x (ce i j w)⟩
  · exact Or.inr ⟨c,cp,c,cp,fun i j x _ w=>d i j (ae i j w) (be i j w) x⟩
  · exact Or.inr ⟨0,hz,0,hz,fun i j _ _ w=>d i j (ae i j w) (be i j w) (ce i j w)⟩

def pick3 (s:List T) (t:T) : Bool :=
  let ws := usable s t
  if ws.any (fun q=>decide (q∈sat s)) then finishAt s t
  else ws.any (fun q=>two (q::s) t (neg t))
theorem pick3Of {s:List T} {t:T} (h:Reach 3 s t) : pick3 s t=true := by
  change (if (usable s t).any (fun q=>decide (q∈sat s)) then finishAt s t else (usable s t).any (fun q=>two (q::s) t (neg t)))=true
  split <;> rename_i flag
  · exact fromTail h
  · cases h with | @step _ _ g _ hg r =>
      rcases separateGate r with old|⟨a,ha,b,hb,dep⟩
      · obtain ⟨a,ha,b,hb,c,hc,d⟩ := old
        have cc : c∈combs s := by simpa using meetmem hc hc
        exact (flag (List.any_eq_true.mpr ⟨c,usableOf ha hb cc d,decide_eq_true hc⟩)).elim
      · apply List.any_eq_true.mpr ⟨g,usableOf ha hb hg dep,?_⟩
        cases r with | step hh r' =>
          cases r' with | step hi r'' =>
            cases r'' with | done hz =>
              exact two_all hh hi hz (by simp [fits,neg])
end GuardDep

namespace K4Core
theorem pickedLower {s} (h : GuardDep.pick3 s tgt=false) : ¬Reach 3 s tgt := by
  intro r
  have q:=GuardDep.pick3Of r
  simp_all
end K4Core

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf0 : ¬Reach 3 [43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf1 : ¬Reach 3 [170,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf2 : ¬Reach 3 [34952,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf3 : ¬Reach 3 [43690,52428,61166,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf4 : ¬Reach 3 [10,170,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf5 : ¬Reach 3 [10,43690,52428,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf6 : ¬Reach 3 [136,170,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf7 : ¬Reach 3 [136,34952,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
def block0 : List (List T) := [[43690,52428,61680,65280],[170,43690,52428,61680,65280],[34952,43690,52428,61680,65280],[43690,52428,61166,61680,65280],[10,170,43690,52428,61680,65280],[10,43690,52428,61680,65280,65520],[136,170,43690,52428,61680,65280],[136,34952,43690,52428,61680,65280]]
theorem blockGood0 : ∀ s∈block0, ¬Reach 3 s tgt := by
  intro s h
  simp only [block0,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf0 | exact leaf1 | exact leaf2 | exact leaf3 | exact leaf4 | exact leaf5 | exact leaf6 | exact leaf7
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf8 : ¬Reach 3 [170,204,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf9 : ¬Reach 3 [170,2570,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf10 : ¬Reach 3 [170,3084,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf11 : ¬Reach 3 [170,3840,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf12 : ¬Reach 3 [170,21760,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf13 : ¬Reach 3 [170,34952,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf14 : ¬Reach 3 [170,43520,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf15 : ¬Reach 3 [170,43690,49344,52428,61680,65280] tgt := pickedLower (by decide +kernel)
def block1 : List (List T) := [[170,204,43690,52428,61680,65280],[170,2570,43690,52428,61680,65280],[170,3084,43690,52428,61680,65280],[170,3840,43690,52428,61680,65280],[170,21760,43690,52428,61680,65280],[170,34952,43690,52428,61680,65280],[170,43520,43690,52428,61680,65280],[170,43690,49344,52428,61680,65280]]
theorem blockGood1 : ∀ s∈block1, ¬Reach 3 s tgt := by
  intro s h
  simp only [block1,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf8 | exact leaf9 | exact leaf10 | exact leaf11 | exact leaf12 | exact leaf13 | exact leaf14 | exact leaf15
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf16 : ¬Reach 3 [170,43690,52224,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf17 : ¬Reach 3 [170,43690,52292,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf18 : ¬Reach 3 [170,43690,52428,52462,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf19 : ¬Reach 3 [170,43690,52428,61166,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf20 : ¬Reach 3 [170,43690,52428,61680,64764,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf21 : ¬Reach 3 [170,43690,52428,61680,65280,65450] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf22 : ¬Reach 3 [170,43690,52428,61680,65280,65484] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf23 : ¬Reach 3 [238,43690,52428,61166,61680,65280] tgt := pickedLower (by decide +kernel)
def block2 : List (List T) := [[170,43690,52224,52428,61680,65280],[170,43690,52292,52428,61680,65280],[170,43690,52428,52462,61680,65280],[170,43690,52428,61166,61680,65280],[170,43690,52428,61680,64764,65280],[170,43690,52428,61680,65280,65450],[170,43690,52428,61680,65280,65484],[238,43690,52428,61166,61680,65280]]
theorem blockGood2 : ∀ s∈block2, ¬Reach 3 s tgt := by
  intro s h
  simp only [block2,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf16 | exact leaf17 | exact leaf18 | exact leaf19 | exact leaf20 | exact leaf21 | exact leaf22 | exact leaf23
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf24 : ¬Reach 3 [2730,43690,52428,61440,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf25 : ¬Reach 3 [32896,34952,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf26 : ¬Reach 3 [34952,41120,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf27 : ¬Reach 3 [34952,43690,52428,61166,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf28 : ¬Reach 3 [34952,43690,52428,61440,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf29 : ¬Reach 3 [34952,43690,52428,61680,63736,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf30 : ¬Reach 3 [34952,43690,52428,61680,64250,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf31 : ¬Reach 3 [34952,43690,52428,61680,65280,65520] tgt := pickedLower (by decide +kernel)
def block3 : List (List T) := [[2730,43690,52428,61440,61680,65280],[32896,34952,43690,52428,61680,65280],[34952,41120,43690,52428,61680,65280],[34952,43690,52428,61166,61680,65280],[34952,43690,52428,61440,61680,65280],[34952,43690,52428,61680,63736,65280],[34952,43690,52428,61680,64250,65280],[34952,43690,52428,61680,65280,65520]]
theorem blockGood3 : ∀ s∈block3, ¬Reach 3 s tgt := by
  intro s h
  simp only [block3,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf24 | exact leaf25 | exact leaf26 | exact leaf27 | exact leaf28 | exact leaf29 | exact leaf30 | exact leaf31
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf32 : ¬Reach 3 [43176,43690,52428,61680,64764,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf33 : ¬Reach 3 [43690,52428,61166,61680,64250,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf34 : ¬Reach 3 [43690,52428,61166,61680,65278,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf35 : ¬Reach 3 [43690,52428,61166,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf36 : ¬Reach 3 [2,10,170,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf37 : ¬Reach 3 [2,10,43690,52428,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf38 : ¬Reach 3 [2,170,43690,52428,61680,64764,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf39 : ¬Reach 3 [2,43690,52428,61680,64764,65280,65532] tgt := pickedLower (by decide +kernel)
def block4 : List (List T) := [[43176,43690,52428,61680,64764,65280],[43690,52428,61166,61680,64250,65280],[43690,52428,61166,61680,65278,65280],[43690,52428,61166,61680,65280,65520],[2,10,170,43690,52428,61680,65280],[2,10,43690,52428,61680,65280,65520],[2,170,43690,52428,61680,64764,65280],[2,43690,52428,61680,64764,65280,65532]]
theorem blockGood4 : ∀ s∈block4, ¬Reach 3 s tgt := by
  intro s h
  simp only [block4,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf32 | exact leaf33 | exact leaf34 | exact leaf35 | exact leaf36 | exact leaf37 | exact leaf38 | exact leaf39
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf40 : ¬Reach 3 [8,10,170,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf41 : ¬Reach 3 [8,10,43690,52428,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf42 : ¬Reach 3 [8,136,170,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf43 : ¬Reach 3 [8,136,34952,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf44 : ¬Reach 3 [8,170,3084,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf45 : ¬Reach 3 [8,34952,43690,52428,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf46 : ¬Reach 3 [10,12,43690,52428,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf47 : ¬Reach 3 [10,34,170,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
def block5 : List (List T) := [[8,10,170,43690,52428,61680,65280],[8,10,43690,52428,61680,65280,65520],[8,136,170,43690,52428,61680,65280],[8,136,34952,43690,52428,61680,65280],[8,170,3084,43690,52428,61680,65280],[8,34952,43690,52428,61680,65280,65520],[10,12,43690,52428,61680,65280,65520],[10,34,170,43690,52428,61680,65280]]
theorem blockGood5 : ∀ s∈block5, ¬Reach 3 s tgt := by
  intro s h
  simp only [block5,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf40 | exact leaf41 | exact leaf42 | exact leaf43 | exact leaf44 | exact leaf45 | exact leaf46 | exact leaf47
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf48 : ¬Reach 3 [10,136,170,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf49 : ¬Reach 3 [10,160,170,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf50 : ¬Reach 3 [10,170,204,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf51 : ¬Reach 3 [10,170,240,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf52 : ¬Reach 3 [10,170,2570,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf53 : ¬Reach 3 [10,170,3084,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf54 : ¬Reach 3 [10,170,3840,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf55 : ¬Reach 3 [10,170,8738,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
def block6 : List (List T) := [[10,136,170,43690,52428,61680,65280],[10,160,170,43690,52428,61680,65280],[10,170,204,43690,52428,61680,65280],[10,170,240,43690,52428,61680,65280],[10,170,2570,43690,52428,61680,65280],[10,170,3084,43690,52428,61680,65280],[10,170,3840,43690,52428,61680,65280],[10,170,8738,43690,52428,61680,65280]]
theorem blockGood6 : ∀ s∈block6, ¬Reach 3 s tgt := by
  intro s h
  simp only [block6,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf48 | exact leaf49 | exact leaf50 | exact leaf51 | exact leaf52 | exact leaf53 | exact leaf54 | exact leaf55
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf56 : ¬Reach 3 [10,170,12336,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf57 : ¬Reach 3 [10,170,13056,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf58 : ¬Reach 3 [10,170,17476,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf59 : ¬Reach 3 [10,170,20560,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf60 : ¬Reach 3 [10,170,21760,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf61 : ¬Reach 3 [10,170,34952,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf62 : ¬Reach 3 [10,170,41120,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf63 : ¬Reach 3 [10,170,43520,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
def block7 : List (List T) := [[10,170,12336,43690,52428,61680,65280],[10,170,13056,43690,52428,61680,65280],[10,170,17476,43690,52428,61680,65280],[10,170,20560,43690,52428,61680,65280],[10,170,21760,43690,52428,61680,65280],[10,170,34952,43690,52428,61680,65280],[10,170,41120,43690,52428,61680,65280],[10,170,43520,43690,52428,61680,65280]]
theorem blockGood7 : ∀ s∈block7, ¬Reach 3 s tgt := by
  intro s h
  simp only [block7,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf56 | exact leaf57 | exact leaf58 | exact leaf59 | exact leaf60 | exact leaf61 | exact leaf62 | exact leaf63
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf64 : ¬Reach 3 [10,170,43680,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf65 : ¬Reach 3 [10,170,43690,49344,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf66 : ¬Reach 3 [10,170,43690,52224,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf67 : ¬Reach 3 [10,170,43690,52292,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf68 : ¬Reach 3 [10,170,43690,52420,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf69 : ¬Reach 3 [10,170,43690,52428,52430,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf70 : ¬Reach 3 [10,170,43690,52428,52462,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf71 : ¬Reach 3 [10,170,43690,52428,61166,61680,65280] tgt := pickedLower (by decide +kernel)
def block8 : List (List T) := [[10,170,43680,43690,52428,61680,65280],[10,170,43690,49344,52428,61680,65280],[10,170,43690,52224,52428,61680,65280],[10,170,43690,52292,52428,61680,65280],[10,170,43690,52420,52428,61680,65280],[10,170,43690,52428,52430,61680,65280],[10,170,43690,52428,52462,61680,65280],[10,170,43690,52428,61166,61680,65280]]
theorem blockGood8 : ∀ s∈block8, ¬Reach 3 s tgt := by
  intro s h
  simp only [block8,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf64 | exact leaf65 | exact leaf66 | exact leaf67 | exact leaf68 | exact leaf69 | exact leaf70 | exact leaf71
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf72 : ¬Reach 3 [10,170,43690,52428,61440,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf73 : ¬Reach 3 [10,170,43690,52428,61520,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf74 : ¬Reach 3 [10,170,43690,52428,61680,61690,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf75 : ¬Reach 3 [10,170,43690,52428,61680,64250,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf76 : ¬Reach 3 [10,170,43690,52428,61680,64764,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf77 : ¬Reach 3 [10,170,43690,52428,61680,65280,65290] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf78 : ¬Reach 3 [10,170,43690,52428,61680,65280,65450] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf79 : ¬Reach 3 [10,170,43690,52428,61680,65280,65484] tgt := pickedLower (by decide +kernel)
def block9 : List (List T) := [[10,170,43690,52428,61440,61680,65280],[10,170,43690,52428,61520,61680,65280],[10,170,43690,52428,61680,61690,65280],[10,170,43690,52428,61680,64250,65280],[10,170,43690,52428,61680,64764,65280],[10,170,43690,52428,61680,65280,65290],[10,170,43690,52428,61680,65280,65450],[10,170,43690,52428,61680,65280,65484]]
theorem blockGood9 : ∀ s∈block9, ¬Reach 3 s tgt := by
  intro s h
  simp only [block9,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf72 | exact leaf73 | exact leaf74 | exact leaf75 | exact leaf76 | exact leaf77 | exact leaf78 | exact leaf79
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf80 : ¬Reach 3 [10,170,43690,52428,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf81 : ¬Reach 3 [10,204,43690,52428,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf82 : ¬Reach 3 [10,240,43530,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf83 : ¬Reach 3 [10,240,43690,52428,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf84 : ¬Reach 3 [10,250,43690,52428,61680,64250,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf85 : ¬Reach 3 [10,8738,43690,52428,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf86 : ¬Reach 3 [10,12336,43690,52428,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf87 : ¬Reach 3 [10,13104,43690,52428,61680,65280,65520] tgt := pickedLower (by decide +kernel)
def block10 : List (List T) := [[10,170,43690,52428,61680,65280,65520],[10,204,43690,52428,61680,65280,65520],[10,240,43530,43690,52428,61680,65280],[10,240,43690,52428,61680,65280,65520],[10,250,43690,52428,61680,64250,65280],[10,8738,43690,52428,61680,65280,65520],[10,12336,43690,52428,61680,65280,65520],[10,13104,43690,52428,61680,65280,65520]]
theorem blockGood10 : ∀ s∈block10, ¬Reach 3 s tgt := by
  intro s h
  simp only [block10,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf80 | exact leaf81 | exact leaf82 | exact leaf83 | exact leaf84 | exact leaf85 | exact leaf86 | exact leaf87
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf88 : ¬Reach 3 [10,17476,43690,52428,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf89 : ¬Reach 3 [10,20560,43690,52428,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf90 : ¬Reach 3 [10,21840,43690,52428,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf91 : ¬Reach 3 [10,34952,43690,52428,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf92 : ¬Reach 3 [10,41120,43690,52428,61680,65280,65440] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf93 : ¬Reach 3 [10,41120,43690,52428,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf94 : ¬Reach 3 [10,43680,43690,52428,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf95 : ¬Reach 3 [10,43690,49344,52428,61680,65280,65520] tgt := pickedLower (by decide +kernel)
def block11 : List (List T) := [[10,17476,43690,52428,61680,65280,65520],[10,20560,43690,52428,61680,65280,65520],[10,21840,43690,52428,61680,65280,65520],[10,34952,43690,52428,61680,65280,65520],[10,41120,43690,52428,61680,65280,65440],[10,41120,43690,52428,61680,65280,65520],[10,43680,43690,52428,61680,65280,65520],[10,43690,49344,52428,61680,65280,65520]]
theorem blockGood11 : ∀ s∈block11, ¬Reach 3 s tgt := by
  intro s h
  simp only [block11,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf88 | exact leaf89 | exact leaf90 | exact leaf91 | exact leaf92 | exact leaf93 | exact leaf94 | exact leaf95
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf96 : ¬Reach 3 [10,43690,52416,52428,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf97 : ¬Reach 3 [10,43690,52420,52428,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf98 : ¬Reach 3 [10,43690,52428,52430,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf99 : ¬Reach 3 [10,43690,52428,61166,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf100 : ¬Reach 3 [10,43690,52428,61440,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf101 : ¬Reach 3 [10,43690,52428,61680,61690,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf102 : ¬Reach 3 [10,43690,52428,61680,64250,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf103 : ¬Reach 3 [10,43690,52428,61680,64764,65280,65520] tgt := pickedLower (by decide +kernel)
def block12 : List (List T) := [[10,43690,52416,52428,61680,65280,65520],[10,43690,52420,52428,61680,65280,65520],[10,43690,52428,52430,61680,65280,65520],[10,43690,52428,61166,61680,65280,65520],[10,43690,52428,61440,61680,65280,65520],[10,43690,52428,61680,61690,65280,65520],[10,43690,52428,61680,64250,65280,65520],[10,43690,52428,61680,64764,65280,65520]]
theorem blockGood12 : ∀ s∈block12, ¬Reach 3 s tgt := by
  intro s h
  simp only [block12,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf96 | exact leaf97 | exact leaf98 | exact leaf99 | exact leaf100 | exact leaf101 | exact leaf102 | exact leaf103
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf104 : ¬Reach 3 [10,43690,52428,61680,65280,65520,65530] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf105 : ¬Reach 3 [10,43690,52428,61680,65280,65520,65532] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf106 : ¬Reach 3 [14,238,43690,52428,61166,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf107 : ¬Reach 3 [14,43690,52428,61166,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf108 : ¬Reach 3 [42,170,43690,49344,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf109 : ¬Reach 3 [42,10794,43690,49344,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf110 : ¬Reach 3 [42,43690,49344,52428,61680,65280,65472] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf111 : ¬Reach 3 [128,136,170,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
def block13 : List (List T) := [[10,43690,52428,61680,65280,65520,65530],[10,43690,52428,61680,65280,65520,65532],[14,238,43690,52428,61166,61680,65280],[14,43690,52428,61166,61680,65280,65520],[42,170,43690,49344,52428,61680,65280],[42,10794,43690,49344,52428,61680,65280],[42,43690,49344,52428,61680,65280,65472],[128,136,170,43690,52428,61680,65280]]
theorem blockGood13 : ∀ s∈block13, ¬Reach 3 s tgt := by
  intro s h
  simp only [block13,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf104 | exact leaf105 | exact leaf106 | exact leaf107 | exact leaf108 | exact leaf109 | exact leaf110 | exact leaf111
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf112 : ¬Reach 3 [128,136,34952,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf113 : ¬Reach 3 [128,170,43690,49344,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf114 : ¬Reach 3 [128,32896,34952,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf115 : ¬Reach 3 [136,160,170,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf116 : ¬Reach 3 [136,170,204,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf117 : ¬Reach 3 [136,170,240,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf118 : ¬Reach 3 [136,170,2570,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf119 : ¬Reach 3 [136,170,3084,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
def block14 : List (List T) := [[128,136,34952,43690,52428,61680,65280],[128,170,43690,49344,52428,61680,65280],[128,32896,34952,43690,52428,61680,65280],[136,160,170,43690,52428,61680,65280],[136,170,204,43690,52428,61680,65280],[136,170,240,43690,52428,61680,65280],[136,170,2570,43690,52428,61680,65280],[136,170,3084,43690,52428,61680,65280]]
theorem blockGood14 : ∀ s∈block14, ¬Reach 3 s tgt := by
  intro s h
  simp only [block14,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf112 | exact leaf113 | exact leaf114 | exact leaf115 | exact leaf116 | exact leaf117 | exact leaf118 | exact leaf119
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf120 : ¬Reach 3 [136,170,3840,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf121 : ¬Reach 3 [136,170,8738,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf122 : ¬Reach 3 [136,170,12336,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf123 : ¬Reach 3 [136,170,13056,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf124 : ¬Reach 3 [136,170,17476,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf125 : ¬Reach 3 [136,170,20560,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf126 : ¬Reach 3 [136,170,21760,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf127 : ¬Reach 3 [136,170,34952,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
def block15 : List (List T) := [[136,170,3840,43690,52428,61680,65280],[136,170,8738,43690,52428,61680,65280],[136,170,12336,43690,52428,61680,65280],[136,170,13056,43690,52428,61680,65280],[136,170,17476,43690,52428,61680,65280],[136,170,20560,43690,52428,61680,65280],[136,170,21760,43690,52428,61680,65280],[136,170,34952,43690,52428,61680,65280]]
theorem blockGood15 : ∀ s∈block15, ¬Reach 3 s tgt := by
  intro s h
  simp only [block15,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf120 | exact leaf121 | exact leaf122 | exact leaf123 | exact leaf124 | exact leaf125 | exact leaf126 | exact leaf127
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf128 : ¬Reach 3 [136,170,41120,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf129 : ¬Reach 3 [136,170,43520,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf130 : ¬Reach 3 [136,170,43554,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf131 : ¬Reach 3 [136,170,43690,49344,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf132 : ¬Reach 3 [136,170,43690,52224,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf133 : ¬Reach 3 [136,170,43690,52292,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf134 : ¬Reach 3 [136,170,43690,52428,52462,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf135 : ¬Reach 3 [136,170,43690,52428,61166,61680,65280] tgt := pickedLower (by decide +kernel)
def block16 : List (List T) := [[136,170,41120,43690,52428,61680,65280],[136,170,43520,43690,52428,61680,65280],[136,170,43554,43690,52428,61680,65280],[136,170,43690,49344,52428,61680,65280],[136,170,43690,52224,52428,61680,65280],[136,170,43690,52292,52428,61680,65280],[136,170,43690,52428,52462,61680,65280],[136,170,43690,52428,61166,61680,65280]]
theorem blockGood16 : ∀ s∈block16, ¬Reach 3 s tgt := by
  intro s h
  simp only [block16,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf128 | exact leaf129 | exact leaf130 | exact leaf131 | exact leaf132 | exact leaf133 | exact leaf134 | exact leaf135
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf136 : ¬Reach 3 [136,170,43690,52428,61440,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf137 : ¬Reach 3 [136,170,43690,52428,61520,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf138 : ¬Reach 3 [136,170,43690,52428,61552,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf139 : ¬Reach 3 [136,170,43690,52428,61680,61688,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf140 : ¬Reach 3 [136,170,43690,52428,61680,61690,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf141 : ¬Reach 3 [136,170,43690,52428,61680,64250,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf142 : ¬Reach 3 [136,170,43690,52428,61680,64764,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf143 : ¬Reach 3 [136,170,43690,52428,61680,65280,65416] tgt := pickedLower (by decide +kernel)
def block17 : List (List T) := [[136,170,43690,52428,61440,61680,65280],[136,170,43690,52428,61520,61680,65280],[136,170,43690,52428,61552,61680,65280],[136,170,43690,52428,61680,61688,65280],[136,170,43690,52428,61680,61690,65280],[136,170,43690,52428,61680,64250,65280],[136,170,43690,52428,61680,64764,65280],[136,170,43690,52428,61680,65280,65416]]
theorem blockGood17 : ∀ s∈block17, ¬Reach 3 s tgt := by
  intro s h
  simp only [block17,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf136 | exact leaf137 | exact leaf138 | exact leaf139 | exact leaf140 | exact leaf141 | exact leaf142 | exact leaf143
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf144 : ¬Reach 3 [136,170,43690,52428,61680,65280,65450] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf145 : ¬Reach 3 [136,170,43690,52428,61680,65280,65484] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf146 : ¬Reach 3 [136,170,43690,52428,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf147 : ¬Reach 3 [136,240,34952,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf148 : ¬Reach 3 [136,2056,34952,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf149 : ¬Reach 3 [136,2570,34952,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf150 : ¬Reach 3 [136,3840,34952,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf151 : ¬Reach 3 [136,8738,34952,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
def block18 : List (List T) := [[136,170,43690,52428,61680,65280,65450],[136,170,43690,52428,61680,65280,65484],[136,170,43690,52428,61680,65280,65520],[136,240,34952,43690,52428,61680,65280],[136,2056,34952,43690,52428,61680,65280],[136,2570,34952,43690,52428,61680,65280],[136,3840,34952,43690,52428,61680,65280],[136,8738,34952,43690,52428,61680,65280]]
theorem blockGood18 : ∀ s∈block18, ¬Reach 3 s tgt := by
  intro s h
  simp only [block18,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf144 | exact leaf145 | exact leaf146 | exact leaf147 | exact leaf148 | exact leaf149 | exact leaf150 | exact leaf151
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf152 : ¬Reach 3 [136,8738,43690,52428,61680,65280,65314] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf153 : ¬Reach 3 [136,8874,43690,52224,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf154 : ¬Reach 3 [136,12336,34952,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf155 : ¬Reach 3 [136,13056,34952,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf156 : ¬Reach 3 [136,28784,34952,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf157 : ¬Reach 3 [136,30464,34952,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf158 : ¬Reach 3 [136,32896,34952,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf159 : ¬Reach 3 [136,34816,34952,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
def block19 : List (List T) := [[136,8738,43690,52428,61680,65280,65314],[136,8874,43690,52224,52428,61680,65280],[136,12336,34952,43690,52428,61680,65280],[136,13056,34952,43690,52428,61680,65280],[136,28784,34952,43690,52428,61680,65280],[136,30464,34952,43690,52428,61680,65280],[136,32896,34952,43690,52428,61680,65280],[136,34816,34952,43690,52428,61680,65280]]
theorem blockGood19 : ∀ s∈block19, ¬Reach 3 s tgt := by
  intro s h
  simp only [block19,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf152 | exact leaf153 | exact leaf154 | exact leaf155 | exact leaf156 | exact leaf157 | exact leaf158 | exact leaf159
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf160 : ¬Reach 3 [136,34952,41120,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf161 : ¬Reach 3 [136,34952,43520,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf162 : ¬Reach 3 [136,34952,43554,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf163 : ¬Reach 3 [136,34952,43690,52428,61166,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf164 : ¬Reach 3 [136,34952,43690,52428,61440,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf165 : ¬Reach 3 [136,34952,43690,52428,61552,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf166 : ¬Reach 3 [136,34952,43690,52428,61680,61688,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf167 : ¬Reach 3 [136,34952,43690,52428,61680,63736,65280] tgt := pickedLower (by decide +kernel)
def block20 : List (List T) := [[136,34952,41120,43690,52428,61680,65280],[136,34952,43520,43690,52428,61680,65280],[136,34952,43554,43690,52428,61680,65280],[136,34952,43690,52428,61166,61680,65280],[136,34952,43690,52428,61440,61680,65280],[136,34952,43690,52428,61552,61680,65280],[136,34952,43690,52428,61680,61688,65280],[136,34952,43690,52428,61680,63736,65280]]
theorem blockGood20 : ∀ s∈block20, ¬Reach 3 s tgt := by
  intro s h
  simp only [block20,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf160 | exact leaf161 | exact leaf162 | exact leaf163 | exact leaf164 | exact leaf165 | exact leaf166 | exact leaf167
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf168 : ¬Reach 3 [136,34952,43690,52428,61680,64250,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf169 : ¬Reach 3 [136,34952,43690,52428,61680,65280,65416] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf170 : ¬Reach 3 [136,34952,43690,52428,61680,65280,65450] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf171 : ¬Reach 3 [136,34952,43690,52428,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf172 : ¬Reach 3 [136,43656,43690,52428,61680,65280,65484] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf173 : ¬Reach 3 [138,170,12336,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf174 : ¬Reach 3 [138,12336,35466,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf175 : ¬Reach 3 [138,12336,43690,52428,61680,65280,65328] tgt := pickedLower (by decide +kernel)
def block21 : List (List T) := [[136,34952,43690,52428,61680,64250,65280],[136,34952,43690,52428,61680,65280,65416],[136,34952,43690,52428,61680,65280,65450],[136,34952,43690,52428,61680,65280,65520],[136,43656,43690,52428,61680,65280,65484],[138,170,12336,43690,52428,61680,65280],[138,12336,35466,43690,52428,61680,65280],[138,12336,43690,52428,61680,65280,65328]]
theorem blockGood21 : ∀ s∈block21, ¬Reach 3 s tgt := by
  intro s h
  simp only [block21,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf168 | exact leaf169 | exact leaf170 | exact leaf171 | exact leaf172 | exact leaf173 | exact leaf174 | exact leaf175
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf176 : ¬Reach 3 [168,170,43690,52428,61680,64764,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf177 : ¬Reach 3 [168,252,43690,52428,61680,64764,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf178 : ¬Reach 3 [168,43176,43690,52428,61680,64764,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf179 : ¬Reach 3 [170,204,238,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf180 : ¬Reach 3 [170,204,240,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf181 : ¬Reach 3 [170,204,2570,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf182 : ¬Reach 3 [170,204,3840,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf183 : ¬Reach 3 [170,204,8738,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
def block22 : List (List T) := [[168,170,43690,52428,61680,64764,65280],[168,252,43690,52428,61680,64764,65280],[168,43176,43690,52428,61680,64764,65280],[170,204,238,43690,52428,61680,65280],[170,204,240,43690,52428,61680,65280],[170,204,2570,43690,52428,61680,65280],[170,204,3840,43690,52428,61680,65280],[170,204,8738,43690,52428,61680,65280]]
theorem blockGood22 : ∀ s∈block22, ¬Reach 3 s tgt := by
  intro s h
  simp only [block22,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf176 | exact leaf177 | exact leaf178 | exact leaf179 | exact leaf180 | exact leaf181 | exact leaf182 | exact leaf183
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf184 : ¬Reach 3 [170,204,12336,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf185 : ¬Reach 3 [170,204,13056,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf186 : ¬Reach 3 [170,204,34952,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf187 : ¬Reach 3 [170,204,41120,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf188 : ¬Reach 3 [170,204,43520,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf189 : ¬Reach 3 [170,204,43554,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf190 : ¬Reach 3 [170,204,43690,43758,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf191 : ¬Reach 3 [170,204,43690,52428,61166,61680,65280] tgt := pickedLower (by decide +kernel)
def block23 : List (List T) := [[170,204,12336,43690,52428,61680,65280],[170,204,13056,43690,52428,61680,65280],[170,204,34952,43690,52428,61680,65280],[170,204,41120,43690,52428,61680,65280],[170,204,43520,43690,52428,61680,65280],[170,204,43554,43690,52428,61680,65280],[170,204,43690,43758,52428,61680,65280],[170,204,43690,52428,61166,61680,65280]]
theorem blockGood23 : ∀ s∈block23, ¬Reach 3 s tgt := by
  intro s h
  simp only [block23,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf184 | exact leaf185 | exact leaf186 | exact leaf187 | exact leaf188 | exact leaf189 | exact leaf190 | exact leaf191
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf192 : ¬Reach 3 [170,204,43690,52428,61440,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf193 : ¬Reach 3 [170,204,43690,52428,61488,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf194 : ¬Reach 3 [170,204,43690,52428,61680,61690,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf195 : ¬Reach 3 [170,204,43690,52428,61680,64250,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf196 : ¬Reach 3 [170,204,43690,52428,61680,65280,65450] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf197 : ¬Reach 3 [170,204,43690,52428,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf198 : ¬Reach 3 [170,238,43690,52428,52462,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf199 : ¬Reach 3 [170,238,43690,52428,61166,61680,65280] tgt := pickedLower (by decide +kernel)
def block24 : List (List T) := [[170,204,43690,52428,61440,61680,65280],[170,204,43690,52428,61488,61680,65280],[170,204,43690,52428,61680,61690,65280],[170,204,43690,52428,61680,64250,65280],[170,204,43690,52428,61680,65280,65450],[170,204,43690,52428,61680,65280,65520],[170,238,43690,52428,52462,61680,65280],[170,238,43690,52428,61166,61680,65280]]
theorem blockGood24 : ∀ s∈block24, ¬Reach 3 s tgt := by
  intro s h
  simp only [block24,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf192 | exact leaf193 | exact leaf194 | exact leaf195 | exact leaf196 | exact leaf197 | exact leaf198 | exact leaf199
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf200 : ¬Reach 3 [170,252,43690,52428,61680,64764,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf201 : ¬Reach 3 [170,2570,2730,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf202 : ¬Reach 3 [170,2570,8738,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf203 : ¬Reach 3 [170,2570,12336,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf204 : ¬Reach 3 [170,2570,17476,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf205 : ¬Reach 3 [170,2570,20560,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf206 : ¬Reach 3 [170,2570,34952,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf207 : ¬Reach 3 [170,2570,41120,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
def block25 : List (List T) := [[170,252,43690,52428,61680,64764,65280],[170,2570,2730,43690,52428,61680,65280],[170,2570,8738,43690,52428,61680,65280],[170,2570,12336,43690,52428,61680,65280],[170,2570,17476,43690,52428,61680,65280],[170,2570,20560,43690,52428,61680,65280],[170,2570,34952,43690,52428,61680,65280],[170,2570,41120,43690,52428,61680,65280]]
theorem blockGood25 : ∀ s∈block25, ¬Reach 3 s tgt := by
  intro s h
  simp only [block25,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf200 | exact leaf201 | exact leaf202 | exact leaf203 | exact leaf204 | exact leaf205 | exact leaf206 | exact leaf207
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf208 : ¬Reach 3 [170,2570,43690,49344,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf209 : ¬Reach 3 [170,2570,43690,50372,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf210 : ¬Reach 3 [170,2570,43690,52428,52462,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf211 : ¬Reach 3 [170,2570,43690,52428,61166,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf212 : ¬Reach 3 [170,2570,43690,52428,61440,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf213 : ¬Reach 3 [170,2570,43690,52428,61520,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf214 : ¬Reach 3 [170,2570,43690,52428,61680,61690,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf215 : ¬Reach 3 [170,2570,43690,52428,61680,64250,65280] tgt := pickedLower (by decide +kernel)
def block26 : List (List T) := [[170,2570,43690,49344,52428,61680,65280],[170,2570,43690,50372,52428,61680,65280],[170,2570,43690,52428,52462,61680,65280],[170,2570,43690,52428,61166,61680,65280],[170,2570,43690,52428,61440,61680,65280],[170,2570,43690,52428,61520,61680,65280],[170,2570,43690,52428,61680,61690,65280],[170,2570,43690,52428,61680,64250,65280]]
theorem blockGood26 : ∀ s∈block26, ¬Reach 3 s tgt := by
  intro s h
  simp only [block26,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf208 | exact leaf209 | exact leaf210 | exact leaf211 | exact leaf212 | exact leaf213 | exact leaf214 | exact leaf215
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf216 : ¬Reach 3 [170,2570,43690,52428,61680,64764,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf217 : ¬Reach 3 [170,2570,43690,52428,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf218 : ¬Reach 3 [170,2730,43690,52428,61440,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf219 : ¬Reach 3 [170,2730,43690,52428,61520,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf220 : ¬Reach 3 [170,3084,3246,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf221 : ¬Reach 3 [170,3084,12336,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf222 : ¬Reach 3 [170,3084,13056,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf223 : ¬Reach 3 [170,3084,34952,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
def block27 : List (List T) := [[170,2570,43690,52428,61680,64764,65280],[170,2570,43690,52428,61680,65280,65520],[170,2730,43690,52428,61440,61680,65280],[170,2730,43690,52428,61520,61680,65280],[170,3084,3246,43690,52428,61680,65280],[170,3084,12336,43690,52428,61680,65280],[170,3084,13056,43690,52428,61680,65280],[170,3084,34952,43690,52428,61680,65280]]
theorem blockGood27 : ∀ s∈block27, ¬Reach 3 s tgt := by
  intro s h
  simp only [block27,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf216 | exact leaf217 | exact leaf218 | exact leaf219 | exact leaf220 | exact leaf221 | exact leaf222 | exact leaf223
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf224 : ¬Reach 3 [170,3084,41120,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf225 : ¬Reach 3 [170,3084,41634,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf226 : ¬Reach 3 [170,3084,43520,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf227 : ¬Reach 3 [170,3084,43690,44718,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf228 : ¬Reach 3 [170,3084,43690,52428,61166,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf229 : ¬Reach 3 [170,3084,43690,52428,61440,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf230 : ¬Reach 3 [170,3084,43690,52428,61520,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf231 : ¬Reach 3 [170,3084,43690,52428,61680,61690,65280] tgt := pickedLower (by decide +kernel)
def block28 : List (List T) := [[170,3084,41120,43690,52428,61680,65280],[170,3084,41634,43690,52428,61680,65280],[170,3084,43520,43690,52428,61680,65280],[170,3084,43690,44718,52428,61680,65280],[170,3084,43690,52428,61166,61680,65280],[170,3084,43690,52428,61440,61680,65280],[170,3084,43690,52428,61520,61680,65280],[170,3084,43690,52428,61680,61690,65280]]
theorem blockGood28 : ∀ s∈block28, ¬Reach 3 s tgt := by
  intro s h
  simp only [block28,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf224 | exact leaf225 | exact leaf226 | exact leaf227 | exact leaf228 | exact leaf229 | exact leaf230 | exact leaf231
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf232 : ¬Reach 3 [170,3084,43690,52428,61680,64250,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf233 : ¬Reach 3 [170,3084,43690,52428,61680,64764,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf234 : ¬Reach 3 [170,3084,43690,52428,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf235 : ¬Reach 3 [170,3086,43690,52428,52462,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf236 : ¬Reach 3 [170,3212,43690,52428,61520,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf237 : ¬Reach 3 [170,3276,43690,52428,61440,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf238 : ¬Reach 3 [170,3598,43690,52428,61166,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf239 : ¬Reach 3 [170,3840,4010,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
def block29 : List (List T) := [[170,3084,43690,52428,61680,64250,65280],[170,3084,43690,52428,61680,64764,65280],[170,3084,43690,52428,61680,65280,65520],[170,3086,43690,52428,52462,61680,65280],[170,3212,43690,52428,61520,61680,65280],[170,3276,43690,52428,61440,61680,65280],[170,3598,43690,52428,61166,61680,65280],[170,3840,4010,43690,52428,61680,65280]]
theorem blockGood29 : ∀ s∈block29, ¬Reach 3 s tgt := by
  intro s h
  simp only [block29,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf232 | exact leaf233 | exact leaf234 | exact leaf235 | exact leaf236 | exact leaf237 | exact leaf238 | exact leaf239
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf240 : ¬Reach 3 [170,3840,20560,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf241 : ¬Reach 3 [170,3840,34952,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf242 : ¬Reach 3 [170,3840,41120,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf243 : ¬Reach 3 [170,3840,41130,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf244 : ¬Reach 3 [170,3840,43520,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf245 : ¬Reach 3 [170,3840,43690,44970,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf246 : ¬Reach 3 [170,3840,43690,49344,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf247 : ¬Reach 3 [170,3840,43690,49356,52428,61680,65280] tgt := pickedLower (by decide +kernel)
def block30 : List (List T) := [[170,3840,20560,43690,52428,61680,65280],[170,3840,34952,43690,52428,61680,65280],[170,3840,41120,43690,52428,61680,65280],[170,3840,41130,43690,52428,61680,65280],[170,3840,43520,43690,52428,61680,65280],[170,3840,43690,44970,52428,61680,65280],[170,3840,43690,49344,52428,61680,65280],[170,3840,43690,49356,52428,61680,65280]]
theorem blockGood30 : ∀ s∈block30, ¬Reach 3 s tgt := by
  intro s h
  simp only [block30,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf240 | exact leaf241 | exact leaf242 | exact leaf243 | exact leaf244 | exact leaf245 | exact leaf246 | exact leaf247
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf248 : ¬Reach 3 [170,3840,43690,52224,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf249 : ¬Reach 3 [170,3840,43690,52292,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf250 : ¬Reach 3 [170,3840,43690,52428,52462,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf251 : ¬Reach 3 [170,3840,43690,52428,53196,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf252 : ¬Reach 3 [170,3840,43690,52428,61166,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf253 : ¬Reach 3 [170,3840,43690,52428,61440,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf254 : ¬Reach 3 [170,3840,43690,52428,61520,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf255 : ¬Reach 3 [170,3840,43690,52428,61680,61690,65280] tgt := pickedLower (by decide +kernel)
def block31 : List (List T) := [[170,3840,43690,52224,52428,61680,65280],[170,3840,43690,52292,52428,61680,65280],[170,3840,43690,52428,52462,61680,65280],[170,3840,43690,52428,53196,61680,65280],[170,3840,43690,52428,61166,61680,65280],[170,3840,43690,52428,61440,61680,65280],[170,3840,43690,52428,61520,61680,65280],[170,3840,43690,52428,61680,61690,65280]]
theorem blockGood31 : ∀ s∈block31, ¬Reach 3 s tgt := by
  intro s h
  simp only [block31,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf248 | exact leaf249 | exact leaf250 | exact leaf251 | exact leaf252 | exact leaf253 | exact leaf254 | exact leaf255
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf256 : ¬Reach 3 [170,3840,43690,52428,61680,64250,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf257 : ¬Reach 3 [170,3840,43690,52428,61680,64764,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf258 : ¬Reach 3 [170,3840,43690,52428,61680,65280,65450] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf259 : ¬Reach 3 [170,3840,43690,52428,61680,65280,65484] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf260 : ¬Reach 3 [170,3840,43690,52428,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf261 : ¬Reach 3 [170,3850,43690,52428,61680,65280,65450] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf262 : ¬Reach 3 [170,3852,43690,52428,61680,65280,65484] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf263 : ¬Reach 3 [170,10794,43690,49344,52428,61680,65280] tgt := pickedLower (by decide +kernel)
def block32 : List (List T) := [[170,3840,43690,52428,61680,64250,65280],[170,3840,43690,52428,61680,64764,65280],[170,3840,43690,52428,61680,65280,65450],[170,3840,43690,52428,61680,65280,65484],[170,3840,43690,52428,61680,65280,65520],[170,3850,43690,52428,61680,65280,65450],[170,3852,43690,52428,61680,65280,65484],[170,10794,43690,49344,52428,61680,65280]]
theorem blockGood32 : ∀ s∈block32, ¬Reach 3 s tgt := by
  intro s h
  simp only [block32,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf256 | exact leaf257 | exact leaf258 | exact leaf259 | exact leaf260 | exact leaf261 | exact leaf262 | exact leaf263
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf264 : ¬Reach 3 [170,16128,43690,49344,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf265 : ¬Reach 3 [170,17612,43520,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf266 : ¬Reach 3 [170,19532,41120,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf267 : ¬Reach 3 [170,21588,43690,52428,61680,64764,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf268 : ¬Reach 3 [170,21760,21930,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf269 : ¬Reach 3 [170,21760,34952,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf270 : ¬Reach 3 [170,21760,35020,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf271 : ¬Reach 3 [170,21760,43520,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
def block33 : List (List T) := [[170,16128,43690,49344,52428,61680,65280],[170,17612,43520,43690,52428,61680,65280],[170,19532,41120,43690,52428,61680,65280],[170,21588,43690,52428,61680,64764,65280],[170,21760,21930,43690,52428,61680,65280],[170,21760,34952,43690,52428,61680,65280],[170,21760,35020,43690,52428,61680,65280],[170,21760,43520,43690,52428,61680,65280]]
theorem blockGood33 : ∀ s∈block33, ¬Reach 3 s tgt := by
  intro s h
  simp only [block33,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf264 | exact leaf265 | exact leaf266 | exact leaf267 | exact leaf268 | exact leaf269 | exact leaf270 | exact leaf271
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf272 : ¬Reach 3 [170,21760,43690,49344,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf273 : ¬Reach 3 [170,21760,43690,52428,52462,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf274 : ¬Reach 3 [170,21760,43690,52428,61166,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf275 : ¬Reach 3 [170,21760,43690,52428,61680,64764,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf276 : ¬Reach 3 [170,21760,43690,52428,61680,65280,65450] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf277 : ¬Reach 3 [170,21828,43690,52428,61680,65280,65484] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf278 : ¬Reach 3 [170,24320,41120,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf279 : ¬Reach 3 [170,32896,34952,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
def block34 : List (List T) := [[170,21760,43690,49344,52428,61680,65280],[170,21760,43690,52428,52462,61680,65280],[170,21760,43690,52428,61166,61680,65280],[170,21760,43690,52428,61680,64764,65280],[170,21760,43690,52428,61680,65280,65450],[170,21828,43690,52428,61680,65280,65484],[170,24320,41120,43690,52428,61680,65280],[170,32896,34952,43690,52428,61680,65280]]
theorem blockGood34 : ∀ s∈block34, ¬Reach 3 s tgt := by
  intro s h
  simp only [block34,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf272 | exact leaf273 | exact leaf274 | exact leaf275 | exact leaf276 | exact leaf277 | exact leaf278 | exact leaf279
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf280 : ¬Reach 3 [170,32896,43690,49344,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf281 : ¬Reach 3 [170,34816,34952,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf282 : ¬Reach 3 [170,34816,43520,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf283 : ¬Reach 3 [170,34816,43690,52224,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf284 : ¬Reach 3 [170,34816,43690,52292,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf285 : ¬Reach 3 [170,34952,34986,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf286 : ¬Reach 3 [170,34952,41120,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf287 : ¬Reach 3 [170,34952,43520,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
def block35 : List (List T) := [[170,32896,43690,49344,52428,61680,65280],[170,34816,34952,43690,52428,61680,65280],[170,34816,43520,43690,52428,61680,65280],[170,34816,43690,52224,52428,61680,65280],[170,34816,43690,52292,52428,61680,65280],[170,34952,34986,43690,52428,61680,65280],[170,34952,41120,43690,52428,61680,65280],[170,34952,43520,43690,52428,61680,65280]]
theorem blockGood35 : ∀ s∈block35, ¬Reach 3 s tgt := by
  intro s h
  simp only [block35,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf280 | exact leaf281 | exact leaf282 | exact leaf283 | exact leaf284 | exact leaf285 | exact leaf286 | exact leaf287
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf288 : ¬Reach 3 [170,34952,43690,49344,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf289 : ¬Reach 3 [170,34952,43690,52224,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf290 : ¬Reach 3 [170,34952,43690,52292,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf291 : ¬Reach 3 [170,34952,43690,52428,52462,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf292 : ¬Reach 3 [170,34952,43690,52428,61166,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf293 : ¬Reach 3 [170,34952,43690,52428,61440,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf294 : ¬Reach 3 [170,34952,43690,52428,61520,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf295 : ¬Reach 3 [170,34952,43690,52428,61680,61690,65280] tgt := pickedLower (by decide +kernel)
def block36 : List (List T) := [[170,34952,43690,49344,52428,61680,65280],[170,34952,43690,52224,52428,61680,65280],[170,34952,43690,52292,52428,61680,65280],[170,34952,43690,52428,52462,61680,65280],[170,34952,43690,52428,61166,61680,65280],[170,34952,43690,52428,61440,61680,65280],[170,34952,43690,52428,61520,61680,65280],[170,34952,43690,52428,61680,61690,65280]]
theorem blockGood36 : ∀ s∈block36, ¬Reach 3 s tgt := by
  intro s h
  simp only [block36,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf288 | exact leaf289 | exact leaf290 | exact leaf291 | exact leaf292 | exact leaf293 | exact leaf294 | exact leaf295
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf296 : ¬Reach 3 [170,34952,43690,52428,61680,63736,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf297 : ¬Reach 3 [170,34952,43690,52428,61680,64250,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf298 : ¬Reach 3 [170,34952,43690,52428,61680,64764,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf299 : ¬Reach 3 [170,34952,43690,52428,61680,65280,65416] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf300 : ¬Reach 3 [170,34952,43690,52428,61680,65280,65450] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf301 : ¬Reach 3 [170,34952,43690,52428,61680,65280,65484] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf302 : ¬Reach 3 [170,34952,43690,52428,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf303 : ¬Reach 3 [170,34986,43690,52428,52462,61680,65280] tgt := pickedLower (by decide +kernel)
def block37 : List (List T) := [[170,34952,43690,52428,61680,63736,65280],[170,34952,43690,52428,61680,64250,65280],[170,34952,43690,52428,61680,64764,65280],[170,34952,43690,52428,61680,65280,65416],[170,34952,43690,52428,61680,65280,65450],[170,34952,43690,52428,61680,65280,65484],[170,34952,43690,52428,61680,65280,65520],[170,34986,43690,52428,52462,61680,65280]]
theorem blockGood37 : ∀ s∈block37, ¬Reach 3 s tgt := by
  intro s h
  simp only [block37,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf296 | exact leaf297 | exact leaf298 | exact leaf299 | exact leaf300 | exact leaf301 | exact leaf302 | exact leaf303
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf304 : ¬Reach 3 [170,43176,43690,52428,61680,64764,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf305 : ¬Reach 3 [170,43520,43690,49344,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf306 : ¬Reach 3 [170,43520,43690,52224,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf307 : ¬Reach 3 [170,43520,43690,52292,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf308 : ¬Reach 3 [170,43520,43690,52428,52462,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf309 : ¬Reach 3 [170,43520,43690,52428,61132,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf310 : ¬Reach 3 [170,43520,43690,52428,61166,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf311 : ¬Reach 3 [170,43520,43690,52428,61680,64764,65280] tgt := pickedLower (by decide +kernel)
def block38 : List (List T) := [[170,43176,43690,52428,61680,64764,65280],[170,43520,43690,49344,52428,61680,65280],[170,43520,43690,52224,52428,61680,65280],[170,43520,43690,52292,52428,61680,65280],[170,43520,43690,52428,52462,61680,65280],[170,43520,43690,52428,61132,61680,65280],[170,43520,43690,52428,61166,61680,65280],[170,43520,43690,52428,61680,64764,65280]]
theorem blockGood38 : ∀ s∈block38, ¬Reach 3 s tgt := by
  intro s h
  simp only [block38,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf304 | exact leaf305 | exact leaf306 | exact leaf307 | exact leaf308 | exact leaf309 | exact leaf310 | exact leaf311
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf312 : ¬Reach 3 [170,43520,43690,52428,61680,65280,65450] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf313 : ¬Reach 3 [170,43520,43690,52428,61680,65280,65484] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf314 : ¬Reach 3 [170,43656,43690,52428,61680,65280,65484] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf315 : ¬Reach 3 [170,43690,49152,49344,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf316 : ¬Reach 3 [170,43690,49152,52224,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf317 : ¬Reach 3 [170,43690,49216,49344,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf318 : ¬Reach 3 [170,43690,49216,52292,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf319 : ¬Reach 3 [170,43690,49344,49386,52428,61680,65280] tgt := pickedLower (by decide +kernel)
def block39 : List (List T) := [[170,43520,43690,52428,61680,65280,65450],[170,43520,43690,52428,61680,65280,65484],[170,43656,43690,52428,61680,65280,65484],[170,43690,49152,49344,52428,61680,65280],[170,43690,49152,52224,52428,61680,65280],[170,43690,49216,49344,52428,61680,65280],[170,43690,49216,52292,52428,61680,65280],[170,43690,49344,49386,52428,61680,65280]]
theorem blockGood39 : ∀ s∈block39, ¬Reach 3 s tgt := by
  intro s h
  simp only [block39,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf312 | exact leaf313 | exact leaf314 | exact leaf315 | exact leaf316 | exact leaf317 | exact leaf318 | exact leaf319
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf320 : ¬Reach 3 [170,43690,49344,52224,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf321 : ¬Reach 3 [170,43690,49344,52292,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf322 : ¬Reach 3 [170,43690,49344,52428,52462,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf323 : ¬Reach 3 [170,43690,49344,52428,60138,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf324 : ¬Reach 3 [170,43690,49344,52428,61166,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf325 : ¬Reach 3 [170,43690,49344,52428,61680,64764,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf326 : ¬Reach 3 [170,43690,49344,52428,61680,65280,65450] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf327 : ¬Reach 3 [170,43690,49344,52428,61680,65280,65472] tgt := pickedLower (by decide +kernel)
def block40 : List (List T) := [[170,43690,49344,52224,52428,61680,65280],[170,43690,49344,52292,52428,61680,65280],[170,43690,49344,52428,52462,61680,65280],[170,43690,49344,52428,60138,61680,65280],[170,43690,49344,52428,61166,61680,65280],[170,43690,49344,52428,61680,64764,65280],[170,43690,49344,52428,61680,65280,65450],[170,43690,49344,52428,61680,65280,65472]]
theorem blockGood40 : ∀ s∈block40, ¬Reach 3 s tgt := by
  intro s h
  simp only [block40,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf320 | exact leaf321 | exact leaf322 | exact leaf323 | exact leaf324 | exact leaf325 | exact leaf326 | exact leaf327
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf328 : ¬Reach 3 [170,43690,49344,52428,61680,65280,65484] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf329 : ¬Reach 3 [170,43690,49352,52428,61680,61690,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf330 : ¬Reach 3 [170,43690,51400,52428,61680,64250,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf331 : ¬Reach 3 [170,43690,52224,52292,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf332 : ¬Reach 3 [170,43690,52224,52394,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf333 : ¬Reach 3 [170,43690,52224,52428,52462,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf334 : ¬Reach 3 [170,43690,52224,52428,61098,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf335 : ¬Reach 3 [170,43690,52224,52428,61166,61680,65280] tgt := pickedLower (by decide +kernel)
def block41 : List (List T) := [[170,43690,49344,52428,61680,65280,65484],[170,43690,49352,52428,61680,61690,65280],[170,43690,51400,52428,61680,64250,65280],[170,43690,52224,52292,52428,61680,65280],[170,43690,52224,52394,52428,61680,65280],[170,43690,52224,52428,52462,61680,65280],[170,43690,52224,52428,61098,61680,65280],[170,43690,52224,52428,61166,61680,65280]]
theorem blockGood41 : ∀ s∈block41, ¬Reach 3 s tgt := by
  intro s h
  simp only [block41,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf328 | exact leaf329 | exact leaf330 | exact leaf331 | exact leaf332 | exact leaf333 | exact leaf334 | exact leaf335
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf336 : ¬Reach 3 [170,43690,52224,52428,61440,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf337 : ¬Reach 3 [170,43690,52224,52428,61520,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf338 : ¬Reach 3 [170,43690,52224,52428,61680,61690,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf339 : ¬Reach 3 [170,43690,52224,52428,61680,64250,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf340 : ¬Reach 3 [170,43690,52224,52428,61680,64752,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf341 : ¬Reach 3 [170,43690,52224,52428,61680,64764,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf342 : ¬Reach 3 [170,43690,52224,52428,61680,65280,65450] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf343 : ¬Reach 3 [170,43690,52224,52428,61680,65280,65484] tgt := pickedLower (by decide +kernel)
def block42 : List (List T) := [[170,43690,52224,52428,61440,61680,65280],[170,43690,52224,52428,61520,61680,65280],[170,43690,52224,52428,61680,61690,65280],[170,43690,52224,52428,61680,64250,65280],[170,43690,52224,52428,61680,64752,65280],[170,43690,52224,52428,61680,64764,65280],[170,43690,52224,52428,61680,65280,65450],[170,43690,52224,52428,61680,65280,65484]]
theorem blockGood42 : ∀ s∈block42, ¬Reach 3 s tgt := by
  intro s h
  simp only [block42,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf336 | exact leaf337 | exact leaf338 | exact leaf339 | exact leaf340 | exact leaf341 | exact leaf342 | exact leaf343
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf344 : ¬Reach 3 [170,43690,52224,52428,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf345 : ¬Reach 3 [170,43690,52292,52428,52462,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf346 : ¬Reach 3 [170,43690,52292,52428,61166,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf347 : ¬Reach 3 [170,43690,52292,52428,61520,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf348 : ¬Reach 3 [170,43690,52292,52428,61680,61690,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf349 : ¬Reach 3 [170,43690,52292,52428,61680,64250,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf350 : ¬Reach 3 [170,43690,52292,52428,61680,64756,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf351 : ¬Reach 3 [170,43690,52292,52428,61680,64764,65280] tgt := pickedLower (by decide +kernel)
def block43 : List (List T) := [[170,43690,52224,52428,61680,65280,65520],[170,43690,52292,52428,52462,61680,65280],[170,43690,52292,52428,61166,61680,65280],[170,43690,52292,52428,61520,61680,65280],[170,43690,52292,52428,61680,61690,65280],[170,43690,52292,52428,61680,64250,65280],[170,43690,52292,52428,61680,64756,65280],[170,43690,52292,52428,61680,64764,65280]]
theorem blockGood43 : ∀ s∈block43, ¬Reach 3 s tgt := by
  intro s h
  simp only [block43,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf344 | exact leaf345 | exact leaf346 | exact leaf347 | exact leaf348 | exact leaf349 | exact leaf350 | exact leaf351
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf352 : ¬Reach 3 [170,43690,52292,52428,61680,65280,65348] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf353 : ¬Reach 3 [170,43690,52292,52428,61680,65280,65450] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf354 : ¬Reach 3 [170,43690,52292,52428,61680,65280,65484] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf355 : ¬Reach 3 [170,43690,52292,52428,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf356 : ¬Reach 3 [170,43690,52360,52428,61680,65280,65450] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf357 : ¬Reach 3 [170,43690,52416,52428,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf358 : ¬Reach 3 [170,43690,52428,52462,61166,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf359 : ¬Reach 3 [170,43690,52428,52462,61680,61690,65280] tgt := pickedLower (by decide +kernel)
def block44 : List (List T) := [[170,43690,52292,52428,61680,65280,65348],[170,43690,52292,52428,61680,65280,65450],[170,43690,52292,52428,61680,65280,65484],[170,43690,52292,52428,61680,65280,65520],[170,43690,52360,52428,61680,65280,65450],[170,43690,52416,52428,61680,65280,65520],[170,43690,52428,52462,61166,61680,65280],[170,43690,52428,52462,61680,61690,65280]]
theorem blockGood44 : ∀ s∈block44, ¬Reach 3 s tgt := by
  intro s h
  simp only [block44,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf352 | exact leaf353 | exact leaf354 | exact leaf355 | exact leaf356 | exact leaf357 | exact leaf358 | exact leaf359
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf360 : ¬Reach 3 [170,43690,52428,52462,61680,64250,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf361 : ¬Reach 3 [170,43690,52428,52462,61680,64764,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf362 : ¬Reach 3 [170,43690,52428,52462,61680,64766,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf363 : ¬Reach 3 [170,43690,52428,52462,61680,65280,65450] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf364 : ¬Reach 3 [170,43690,52428,52462,61680,65280,65484] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf365 : ¬Reach 3 [170,43690,52428,52462,61680,65280,65518] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf366 : ¬Reach 3 [170,43690,52428,52462,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf367 : ¬Reach 3 [170,43690,52428,60928,61166,61680,65280] tgt := pickedLower (by decide +kernel)
def block45 : List (List T) := [[170,43690,52428,52462,61680,64250,65280],[170,43690,52428,52462,61680,64764,65280],[170,43690,52428,52462,61680,64766,65280],[170,43690,52428,52462,61680,65280,65450],[170,43690,52428,52462,61680,65280,65484],[170,43690,52428,52462,61680,65280,65518],[170,43690,52428,52462,61680,65280,65520],[170,43690,52428,60928,61166,61680,65280]]
theorem blockGood45 : ∀ s∈block45, ¬Reach 3 s tgt := by
  intro s h
  simp only [block45,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf360 | exact leaf361 | exact leaf362 | exact leaf363 | exact leaf364 | exact leaf365 | exact leaf366 | exact leaf367
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf368 : ¬Reach 3 [170,43690,52428,60996,61166,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf369 : ¬Reach 3 [170,43690,52428,61166,61680,64250,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf370 : ¬Reach 3 [170,43690,52428,61166,61680,64764,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf371 : ¬Reach 3 [170,43690,52428,61166,61680,65278,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf372 : ¬Reach 3 [170,43690,52428,61166,61680,65280,65450] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf373 : ¬Reach 3 [170,43690,52428,61166,61680,65280,65484] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf374 : ¬Reach 3 [170,43690,52428,61166,61680,65280,65518] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf375 : ¬Reach 3 [170,43690,52428,61166,61680,65280,65520] tgt := pickedLower (by decide +kernel)
def block46 : List (List T) := [[170,43690,52428,60996,61166,61680,65280],[170,43690,52428,61166,61680,64250,65280],[170,43690,52428,61166,61680,64764,65280],[170,43690,52428,61166,61680,65278,65280],[170,43690,52428,61166,61680,65280,65450],[170,43690,52428,61166,61680,65280,65484],[170,43690,52428,61166,61680,65280,65518],[170,43690,52428,61166,61680,65280,65520]]
theorem blockGood46 : ∀ s∈block46, ¬Reach 3 s tgt := by
  intro s h
  simp only [block46,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf368 | exact leaf369 | exact leaf370 | exact leaf371 | exact leaf372 | exact leaf373 | exact leaf374 | exact leaf375
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf376 : ¬Reach 3 [170,43690,52428,61680,64512,64764,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf377 : ¬Reach 3 [170,43690,52428,61680,64596,64764,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf378 : ¬Reach 3 [170,43690,52428,61680,64764,64766,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf379 : ¬Reach 3 [170,43690,52428,61680,64764,65278,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf380 : ¬Reach 3 [170,43690,52428,61680,64764,65280,65450] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf381 : ¬Reach 3 [170,43690,52428,61680,64764,65280,65484] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf382 : ¬Reach 3 [170,43690,52428,61680,64764,65280,65532] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf383 : ¬Reach 3 [170,43690,52428,61680,65280,65348,65484] tgt := pickedLower (by decide +kernel)
def block47 : List (List T) := [[170,43690,52428,61680,64512,64764,65280],[170,43690,52428,61680,64596,64764,65280],[170,43690,52428,61680,64764,64766,65280],[170,43690,52428,61680,64764,65278,65280],[170,43690,52428,61680,64764,65280,65450],[170,43690,52428,61680,64764,65280,65484],[170,43690,52428,61680,64764,65280,65532],[170,43690,52428,61680,65280,65348,65484]]
theorem blockGood47 : ∀ s∈block47, ¬Reach 3 s tgt := by
  intro s h
  simp only [block47,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf376 | exact leaf377 | exact leaf378 | exact leaf379 | exact leaf380 | exact leaf381 | exact leaf382 | exact leaf383
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf384 : ¬Reach 3 [170,43690,52428,61680,65280,65450,65484] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf385 : ¬Reach 3 [170,43690,52428,61680,65280,65450,65518] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf386 : ¬Reach 3 [170,43690,52428,61680,65280,65484,65518] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf387 : ¬Reach 3 [170,43690,52428,61680,65280,65484,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf388 : ¬Reach 3 [170,43690,52428,61680,65280,65484,65532] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf389 : ¬Reach 3 [234,43690,49344,52428,60138,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf390 : ¬Reach 3 [238,3598,43690,52428,61166,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf391 : ¬Reach 3 [238,34952,43690,52428,61166,61680,65280] tgt := pickedLower (by decide +kernel)
def block48 : List (List T) := [[170,43690,52428,61680,65280,65450,65484],[170,43690,52428,61680,65280,65450,65518],[170,43690,52428,61680,65280,65484,65518],[170,43690,52428,61680,65280,65484,65520],[170,43690,52428,61680,65280,65484,65532],[234,43690,49344,52428,60138,61680,65280],[238,3598,43690,52428,61166,61680,65280],[238,34952,43690,52428,61166,61680,65280]]
theorem blockGood48 : ∀ s∈block48, ¬Reach 3 s tgt := by
  intro s h
  simp only [block48,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf384 | exact leaf385 | exact leaf386 | exact leaf387 | exact leaf388 | exact leaf389 | exact leaf390 | exact leaf391
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf392 : ¬Reach 3 [238,41120,43690,52428,61166,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf393 : ¬Reach 3 [238,43520,43690,52428,61166,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf394 : ¬Reach 3 [238,43690,43758,52428,61166,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf395 : ¬Reach 3 [238,43690,52428,57568,61166,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf396 : ¬Reach 3 [238,43690,52428,60928,61166,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf397 : ¬Reach 3 [238,43690,52428,61166,61440,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf398 : ¬Reach 3 [238,43690,52428,61166,61456,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf399 : ¬Reach 3 [238,43690,52428,61166,61680,61694,65280] tgt := pickedLower (by decide +kernel)
def block49 : List (List T) := [[238,41120,43690,52428,61166,61680,65280],[238,43520,43690,52428,61166,61680,65280],[238,43690,43758,52428,61166,61680,65280],[238,43690,52428,57568,61166,61680,65280],[238,43690,52428,60928,61166,61680,65280],[238,43690,52428,61166,61440,61680,65280],[238,43690,52428,61166,61456,61680,65280],[238,43690,52428,61166,61680,61694,65280]]
theorem blockGood49 : ∀ s∈block49, ¬Reach 3 s tgt := by
  intro s h
  simp only [block49,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf392 | exact leaf393 | exact leaf394 | exact leaf395 | exact leaf396 | exact leaf397 | exact leaf398 | exact leaf399
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf400 : ¬Reach 3 [238,43690,52428,61166,61680,64250,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf401 : ¬Reach 3 [238,43690,52428,61166,61680,65278,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf402 : ¬Reach 3 [238,43690,52428,61166,61680,65280,65450] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf403 : ¬Reach 3 [238,43690,52428,61166,61680,65280,65518] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf404 : ¬Reach 3 [238,43690,52428,61166,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf405 : ¬Reach 3 [238,43690,52428,61680,65280,65450,65518] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf406 : ¬Reach 3 [254,43690,52428,61166,61680,65278,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf407 : ¬Reach 3 [682,43690,52428,61680,64512,64764,65280] tgt := pickedLower (by decide +kernel)
def block50 : List (List T) := [[238,43690,52428,61166,61680,64250,65280],[238,43690,52428,61166,61680,65278,65280],[238,43690,52428,61166,61680,65280,65450],[238,43690,52428,61166,61680,65280,65518],[238,43690,52428,61166,61680,65280,65520],[238,43690,52428,61680,65280,65450,65518],[254,43690,52428,61166,61680,65278,65280],[682,43690,52428,61680,64512,64764,65280]]
theorem blockGood50 : ∀ s∈block50, ¬Reach 3 s tgt := by
  intro s h
  simp only [block50,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf400 | exact leaf401 | exact leaf402 | exact leaf403 | exact leaf404 | exact leaf405 | exact leaf406 | exact leaf407
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf408 : ¬Reach 3 [2184,2730,43690,52428,61440,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf409 : ¬Reach 3 [2184,34952,43690,52428,61440,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf410 : ¬Reach 3 [2730,3276,43690,52428,61440,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf411 : ¬Reach 3 [2730,34952,43690,52428,61440,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf412 : ¬Reach 3 [2730,40960,41120,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf413 : ¬Reach 3 [2730,40960,43690,52428,61440,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf414 : ¬Reach 3 [2730,41120,43690,52428,61440,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf415 : ¬Reach 3 [2730,43690,49152,52428,61440,61680,65280] tgt := pickedLower (by decide +kernel)
def block51 : List (List T) := [[2184,2730,43690,52428,61440,61680,65280],[2184,34952,43690,52428,61440,61680,65280],[2730,3276,43690,52428,61440,61680,65280],[2730,34952,43690,52428,61440,61680,65280],[2730,40960,41120,43690,52428,61680,65280],[2730,40960,43690,52428,61440,61680,65280],[2730,41120,43690,52428,61440,61680,65280],[2730,43690,49152,52428,61440,61680,65280]]
theorem blockGood51 : ∀ s∈block51, ¬Reach 3 s tgt := by
  intro s h
  simp only [block51,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf408 | exact leaf409 | exact leaf410 | exact leaf411 | exact leaf412 | exact leaf413 | exact leaf414 | exact leaf415
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf416 : ¬Reach 3 [2730,43690,49344,52428,61440,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf417 : ¬Reach 3 [2730,43690,50244,52428,61440,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf418 : ¬Reach 3 [2730,43690,52428,52974,61440,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf419 : ¬Reach 3 [2730,43690,52428,61166,61440,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf420 : ¬Reach 3 [2730,43690,52428,61440,61520,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf421 : ¬Reach 3 [2730,43690,52428,61440,61680,64170,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf422 : ¬Reach 3 [2730,43690,52428,61440,61680,64250,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf423 : ¬Reach 3 [2730,43690,52428,61440,61680,64716,65280] tgt := pickedLower (by decide +kernel)
def block52 : List (List T) := [[2730,43690,49344,52428,61440,61680,65280],[2730,43690,50244,52428,61440,61680,65280],[2730,43690,52428,52974,61440,61680,65280],[2730,43690,52428,61166,61440,61680,65280],[2730,43690,52428,61440,61520,61680,65280],[2730,43690,52428,61440,61680,64170,65280],[2730,43690,52428,61440,61680,64250,65280],[2730,43690,52428,61440,61680,64716,65280]]
theorem blockGood52 : ∀ s∈block52, ¬Reach 3 s tgt := by
  intro s h
  simp only [block52,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf416 | exact leaf417 | exact leaf418 | exact leaf419 | exact leaf420 | exact leaf421 | exact leaf422 | exact leaf423
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf424 : ¬Reach 3 [2730,43690,52428,61440,61680,64764,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf425 : ¬Reach 3 [2730,43690,52428,61440,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf426 : ¬Reach 3 [2810,43690,52428,61440,61680,64250,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf427 : ¬Reach 3 [3822,43690,52428,61166,61440,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf428 : ¬Reach 3 [4080,43690,52428,61440,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf429 : ¬Reach 3 [10922,43690,49152,49344,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf430 : ¬Reach 3 [32768,32896,34952,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf431 : ¬Reach 3 [32768,34952,43690,52428,61440,61680,65280] tgt := pickedLower (by decide +kernel)
def block53 : List (List T) := [[2730,43690,52428,61440,61680,64764,65280],[2730,43690,52428,61440,61680,65280,65520],[2810,43690,52428,61440,61680,64250,65280],[3822,43690,52428,61166,61440,61680,65280],[4080,43690,52428,61440,61680,65280,65520],[10922,43690,49152,49344,52428,61680,65280],[32768,32896,34952,43690,52428,61680,65280],[32768,34952,43690,52428,61440,61680,65280]]
theorem blockGood53 : ∀ s∈block53, ¬Reach 3 s tgt := by
  intro s h
  simp only [block53,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf424 | exact leaf425 | exact leaf426 | exact leaf427 | exact leaf428 | exact leaf429 | exact leaf430 | exact leaf431
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf432 : ¬Reach 3 [32896,34816,34952,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf433 : ¬Reach 3 [32896,34952,41120,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf434 : ¬Reach 3 [32896,34952,43520,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf435 : ¬Reach 3 [32896,34952,43690,52428,61166,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf436 : ¬Reach 3 [32896,34952,43690,52428,61440,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf437 : ¬Reach 3 [32896,34952,43690,52428,61680,63736,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf438 : ¬Reach 3 [32896,34952,43690,52428,61680,64250,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf439 : ¬Reach 3 [32896,34952,43690,52428,61680,65280,65408] tgt := pickedLower (by decide +kernel)
def block54 : List (List T) := [[32896,34816,34952,43690,52428,61680,65280],[32896,34952,41120,43690,52428,61680,65280],[32896,34952,43520,43690,52428,61680,65280],[32896,34952,43690,52428,61166,61680,65280],[32896,34952,43690,52428,61440,61680,65280],[32896,34952,43690,52428,61680,63736,65280],[32896,34952,43690,52428,61680,64250,65280],[32896,34952,43690,52428,61680,65280,65408]]
theorem blockGood54 : ∀ s∈block54, ¬Reach 3 s tgt := by
  intro s h
  simp only [block54,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf432 | exact leaf433 | exact leaf434 | exact leaf435 | exact leaf436 | exact leaf437 | exact leaf438 | exact leaf439
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf440 : ¬Reach 3 [32896,34952,43690,52428,61680,65280,65416] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf441 : ¬Reach 3 [32896,34952,43690,52428,61680,65280,65450] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf442 : ¬Reach 3 [32896,34952,43690,52428,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf443 : ¬Reach 3 [34944,34952,43690,52428,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf444 : ¬Reach 3 [34944,43680,43690,52428,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf445 : ¬Reach 3 [34952,41120,43176,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf446 : ¬Reach 3 [34952,41120,43520,43690,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf447 : ¬Reach 3 [34952,41120,43690,49344,52428,61680,65280] tgt := pickedLower (by decide +kernel)
def block55 : List (List T) := [[32896,34952,43690,52428,61680,65280,65416],[32896,34952,43690,52428,61680,65280,65450],[32896,34952,43690,52428,61680,65280,65520],[34944,34952,43690,52428,61680,65280,65520],[34944,43680,43690,52428,61680,65280,65520],[34952,41120,43176,43690,52428,61680,65280],[34952,41120,43520,43690,52428,61680,65280],[34952,41120,43690,49344,52428,61680,65280]]
theorem blockGood55 : ∀ s∈block55, ¬Reach 3 s tgt := by
  intro s h
  simp only [block55,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf440 | exact leaf441 | exact leaf442 | exact leaf443 | exact leaf444 | exact leaf445 | exact leaf446 | exact leaf447
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf448 : ¬Reach 3 [34952,41120,43690,52224,52428,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf449 : ¬Reach 3 [34952,41120,43690,52428,60652,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf450 : ¬Reach 3 [34952,41120,43690,52428,61166,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf451 : ¬Reach 3 [34952,41120,43690,52428,61680,64764,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf452 : ¬Reach 3 [34952,41120,43690,52428,61680,65280,65416] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf453 : ¬Reach 3 [34952,41120,43690,52428,61680,65280,65450] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf454 : ¬Reach 3 [34952,41120,43690,52428,61680,65280,65484] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf455 : ¬Reach 3 [34952,43176,43690,52428,61680,63736,65280] tgt := pickedLower (by decide +kernel)
def block56 : List (List T) := [[34952,41120,43690,52224,52428,61680,65280],[34952,41120,43690,52428,60652,61680,65280],[34952,41120,43690,52428,61166,61680,65280],[34952,41120,43690,52428,61680,64764,65280],[34952,41120,43690,52428,61680,65280,65416],[34952,41120,43690,52428,61680,65280,65450],[34952,41120,43690,52428,61680,65280,65484],[34952,43176,43690,52428,61680,63736,65280]]
theorem blockGood56 : ∀ s∈block56, ¬Reach 3 s tgt := by
  intro s h
  simp only [block56,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf448 | exact leaf449 | exact leaf450 | exact leaf451 | exact leaf452 | exact leaf453 | exact leaf454 | exact leaf455
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf456 : ¬Reach 3 [34952,43176,43690,52428,61680,64764,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf457 : ¬Reach 3 [34952,43680,43690,52428,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf458 : ¬Reach 3 [34952,43690,52428,57568,61166,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf459 : ¬Reach 3 [34952,43690,52428,61166,61440,61680,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf460 : ¬Reach 3 [34952,43690,52428,61166,61680,63736,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf461 : ¬Reach 3 [34952,43690,52428,61166,61680,64250,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf462 : ¬Reach 3 [34952,43690,52428,61166,61680,65278,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf463 : ¬Reach 3 [34952,43690,52428,61166,61680,65280,65520] tgt := pickedLower (by decide +kernel)
def block57 : List (List T) := [[34952,43176,43690,52428,61680,64764,65280],[34952,43680,43690,52428,61680,65280,65520],[34952,43690,52428,57568,61166,61680,65280],[34952,43690,52428,61166,61440,61680,65280],[34952,43690,52428,61166,61680,63736,65280],[34952,43690,52428,61166,61680,64250,65280],[34952,43690,52428,61166,61680,65278,65280],[34952,43690,52428,61166,61680,65280,65520]]
theorem blockGood57 : ∀ s∈block57, ¬Reach 3 s tgt := by
  intro s h
  simp only [block57,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf456 | exact leaf457 | exact leaf458 | exact leaf459 | exact leaf460 | exact leaf461 | exact leaf462 | exact leaf463
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf464 : ¬Reach 3 [34952,43690,52428,61440,61680,63624,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf465 : ¬Reach 3 [34952,43690,52428,61440,61680,63736,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf466 : ¬Reach 3 [34952,43690,52428,61440,61680,64250,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf467 : ¬Reach 3 [34952,43690,52428,61568,61680,65280,65416] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf468 : ¬Reach 3 [34952,43690,52428,61600,61680,65280,65450] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf469 : ¬Reach 3 [34952,43690,52428,61680,63736,64250,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf470 : ¬Reach 3 [34952,43690,52428,61680,63736,65280,65416] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf471 : ¬Reach 3 [34952,43690,52428,61680,63736,65280,65450] tgt := pickedLower (by decide +kernel)
def block58 : List (List T) := [[34952,43690,52428,61440,61680,63624,65280],[34952,43690,52428,61440,61680,63736,65280],[34952,43690,52428,61440,61680,64250,65280],[34952,43690,52428,61568,61680,65280,65416],[34952,43690,52428,61600,61680,65280,65450],[34952,43690,52428,61680,63736,64250,65280],[34952,43690,52428,61680,63736,65280,65416],[34952,43690,52428,61680,63736,65280,65450]]
theorem blockGood58 : ∀ s∈block58, ¬Reach 3 s tgt := by
  intro s h
  simp only [block58,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf464 | exact leaf465 | exact leaf466 | exact leaf467 | exact leaf468 | exact leaf469 | exact leaf470 | exact leaf471
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf472 : ¬Reach 3 [34952,43690,52428,61680,63736,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf473 : ¬Reach 3 [34952,43690,52428,61680,63736,65280,65528] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf474 : ¬Reach 3 [34952,43690,52428,61680,64250,64764,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf475 : ¬Reach 3 [34952,43690,52428,61680,64250,65278,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf476 : ¬Reach 3 [34952,43690,52428,61680,64250,65280,65450] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf477 : ¬Reach 3 [34952,43690,52428,61680,64250,65280,65484] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf478 : ¬Reach 3 [34952,43690,52428,61680,64250,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf479 : ¬Reach 3 [34952,43690,52428,61680,64250,65280,65530] tgt := pickedLower (by decide +kernel)
def block59 : List (List T) := [[34952,43690,52428,61680,63736,65280,65520],[34952,43690,52428,61680,63736,65280,65528],[34952,43690,52428,61680,64250,64764,65280],[34952,43690,52428,61680,64250,65278,65280],[34952,43690,52428,61680,64250,65280,65450],[34952,43690,52428,61680,64250,65280,65484],[34952,43690,52428,61680,64250,65280,65520],[34952,43690,52428,61680,64250,65280,65530]]
theorem blockGood59 : ∀ s∈block59, ¬Reach 3 s tgt := by
  intro s h
  simp only [block59,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf472 | exact leaf473 | exact leaf474 | exact leaf475 | exact leaf476 | exact leaf477 | exact leaf478 | exact leaf479
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf480 : ¬Reach 3 [34952,43690,52428,61680,65280,65520,65528] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf481 : ¬Reach 3 [34952,43690,52428,61680,65280,65520,65530] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf482 : ¬Reach 3 [43176,43690,52428,60652,61680,64764,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf483 : ¬Reach 3 [43176,43690,52428,61166,61680,64764,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf484 : ¬Reach 3 [43176,43690,52428,61680,64512,64764,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf485 : ¬Reach 3 [43176,43690,52428,61680,64764,65278,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf486 : ¬Reach 3 [43176,43690,52428,61680,64764,65280,65448] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf487 : ¬Reach 3 [43176,43690,52428,61680,64764,65280,65450] tgt := pickedLower (by decide +kernel)
def block60 : List (List T) := [[34952,43690,52428,61680,65280,65520,65528],[34952,43690,52428,61680,65280,65520,65530],[43176,43690,52428,60652,61680,64764,65280],[43176,43690,52428,61166,61680,64764,65280],[43176,43690,52428,61680,64512,64764,65280],[43176,43690,52428,61680,64764,65278,65280],[43176,43690,52428,61680,64764,65280,65448],[43176,43690,52428,61680,64764,65280,65450]]
theorem blockGood60 : ∀ s∈block60, ¬Reach 3 s tgt := by
  intro s h
  simp only [block60,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf480 | exact leaf481 | exact leaf482 | exact leaf483 | exact leaf484 | exact leaf485 | exact leaf486 | exact leaf487
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf488 : ¬Reach 3 [43176,43690,52428,61680,64764,65280,65484] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf489 : ¬Reach 3 [43176,43690,52428,61680,64764,65280,65532] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf490 : ¬Reach 3 [43688,43690,52428,61680,64764,65280,65532] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf491 : ¬Reach 3 [43690,52428,60138,61166,61680,64250,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf492 : ¬Reach 3 [43690,52428,61152,61166,61680,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf493 : ¬Reach 3 [43690,52428,61166,61680,64250,64764,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf494 : ¬Reach 3 [43690,52428,61166,61680,64250,65278,65280] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf495 : ¬Reach 3 [43690,52428,61166,61680,64250,65280,65450] tgt := pickedLower (by decide +kernel)
def block61 : List (List T) := [[43176,43690,52428,61680,64764,65280,65484],[43176,43690,52428,61680,64764,65280,65532],[43688,43690,52428,61680,64764,65280,65532],[43690,52428,60138,61166,61680,64250,65280],[43690,52428,61152,61166,61680,65280,65520],[43690,52428,61166,61680,64250,64764,65280],[43690,52428,61166,61680,64250,65278,65280],[43690,52428,61166,61680,64250,65280,65450]]
theorem blockGood61 : ∀ s∈block61, ¬Reach 3 s tgt := by
  intro s h
  simp only [block61,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf488 | exact leaf489 | exact leaf490 | exact leaf491 | exact leaf492 | exact leaf493 | exact leaf494 | exact leaf495
end K4Num

namespace K4Num
open K4Core
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf496 : ¬Reach 3 [43690,52428,61166,61680,64250,65280,65484] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf497 : ¬Reach 3 [43690,52428,61166,61680,64250,65280,65518] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf498 : ¬Reach 3 [43690,52428,61166,61680,65278,65280,65518] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf499 : ¬Reach 3 [43690,52428,61166,61680,65278,65280,65520] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf500 : ¬Reach 3 [43690,52428,61166,61680,65278,65280,65534] tgt := pickedLower (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem leaf501 : ¬Reach 3 [43690,52428,61166,61680,65280,65520,65534] tgt := pickedLower (by decide +kernel)
def block62 : List (List T) := [[43690,52428,61166,61680,64250,65280,65484],[43690,52428,61166,61680,64250,65280,65518],[43690,52428,61166,61680,65278,65280,65518],[43690,52428,61166,61680,65278,65280,65520],[43690,52428,61166,61680,65278,65280,65534],[43690,52428,61166,61680,65280,65520,65534]]
theorem blockGood62 : ∀ s∈block62, ¬Reach 3 s tgt := by
  intro s h
  simp only [block62,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact leaf496 | exact leaf497 | exact leaf498 | exact leaf499 | exact leaf500 | exact leaf501
end K4Num

namespace K4Num
open K4Core
structure SafeBlock where
  states : List (List T)
  valid : ∀ s∈states, ¬ Reach 3 s tgt
def batches : List SafeBlock := [
  ⟨block0,blockGood0⟩,
  ⟨block1,blockGood1⟩,
  ⟨block2,blockGood2⟩,
  ⟨block3,blockGood3⟩,
  ⟨block4,blockGood4⟩,
  ⟨block5,blockGood5⟩,
  ⟨block6,blockGood6⟩,
  ⟨block7,blockGood7⟩,
  ⟨block8,blockGood8⟩,
  ⟨block9,blockGood9⟩,
  ⟨block10,blockGood10⟩,
  ⟨block11,blockGood11⟩,
  ⟨block12,blockGood12⟩,
  ⟨block13,blockGood13⟩,
  ⟨block14,blockGood14⟩,
  ⟨block15,blockGood15⟩,
  ⟨block16,blockGood16⟩,
  ⟨block17,blockGood17⟩,
  ⟨block18,blockGood18⟩,
  ⟨block19,blockGood19⟩,
  ⟨block20,blockGood20⟩,
  ⟨block21,blockGood21⟩,
  ⟨block22,blockGood22⟩,
  ⟨block23,blockGood23⟩,
  ⟨block24,blockGood24⟩,
  ⟨block25,blockGood25⟩,
  ⟨block26,blockGood26⟩,
  ⟨block27,blockGood27⟩,
  ⟨block28,blockGood28⟩,
  ⟨block29,blockGood29⟩,
  ⟨block30,blockGood30⟩,
  ⟨block31,blockGood31⟩,
  ⟨block32,blockGood32⟩,
  ⟨block33,blockGood33⟩,
  ⟨block34,blockGood34⟩,
  ⟨block35,blockGood35⟩,
  ⟨block36,blockGood36⟩,
  ⟨block37,blockGood37⟩,
  ⟨block38,blockGood38⟩,
  ⟨block39,blockGood39⟩,
  ⟨block40,blockGood40⟩,
  ⟨block41,blockGood41⟩,
  ⟨block42,blockGood42⟩,
  ⟨block43,blockGood43⟩,
  ⟨block44,blockGood44⟩,
  ⟨block45,blockGood45⟩,
  ⟨block46,blockGood46⟩,
  ⟨block47,blockGood47⟩,
  ⟨block48,blockGood48⟩,
  ⟨block49,blockGood49⟩,
  ⟨block50,blockGood50⟩,
  ⟨block51,blockGood51⟩,
  ⟨block52,blockGood52⟩,
  ⟨block53,blockGood53⟩,
  ⟨block54,blockGood54⟩,
  ⟨block55,blockGood55⟩,
  ⟨block56,blockGood56⟩,
  ⟨block57,blockGood57⟩,
  ⟨block58,blockGood58⟩,
  ⟨block59,blockGood59⟩,
  ⟨block60,blockGood60⟩,
  ⟨block61,blockGood61⟩,
  ⟨block62,blockGood62⟩]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem allLower : ¬ Reach 6 [43690,52428,61680,65280] tgt := by
  apply K4Orbit.orbitLower
  intro s hs
  have e : K4Orbit.stages3 = batches.flatMap SafeBlock.states := by rfl
  rw [e] at hs
  obtain ⟨b,_,h⟩ := List.mem_flatMap.mp hs
  exact b.valid _ h
end K4Num

namespace K4Six
abbrev T := BitVec 16
abbrev Addr := BitVec 4
def pool : List T := [43690,52428,61680,65280]
def target : T := 65256
def pick (a : Addr) : List T→T
  | [] => 0
  | x::xs => if a=0 then x else pick (a-1) xs
def lit (inv : Bool) (v : T) : T := if inv then ~~~v else v
structure Code where
  a : Addr
  b : Addr
  na : Bool
  nb : Bool
def step (c : Code) (s : List T) : List T :=
  (lit c.na (pick c.a s) &&& lit c.nb (pick c.b s))::s
def endValue (s : List T) := s.headD 0
theorem pick_mem (a:Addr) (s:List T) : pick a s = 0 ∨ pick a s ∈ s := by
  induction s generalizing a with
  | nil => exact Or.inl rfl
  | cons x xs ih =>
    unfold pick
    split
    · exact Or.inr (List.mem_cons_self ..)
    · exact (ih (a-1)).imp_right (List.mem_cons_of_mem x)

theorem lit_mem (a:Addr) (b:Bool) (s:List T) : lit b (pick a s) ∈ K4Core.sat s := by
  have h : pick a s ∈ K4Core.sat s := by
    rcases pick_mem a s with n|m
    · simp [n,K4Core.sat]
    · simp [m,K4Core.sat]
  cases b with
  | false => exact h
  | true => exact K4Core.negmem h

theorem step_reach (c:Code) {k s z} (h:K4Core.Reach k (step c s) z) :
    K4Core.Reach (k+1) s z :=
  .step (K4Core.meetmem (lit_mem _ _ _) (lit_mem _ _ _)) h

theorem fromSearch (no : ¬K4Core.Reach 6 pool K4Core.tgt) (c0 c1 c2 c3 c4 c5 : Code) :
  let z := endValue (step c5 (step c4 (step c3 (step c2 (step c1 (step c0 pool))))))
  z≠target ∧ (~~~z)≠target := by
  dsimp only
  let s := step c5 (step c4 (step c3 (step c2 (step c1 (step c0 pool)))))
  have hz : endValue s ∈ K4Core.sat s := by
    simp [s,endValue,step,K4Core.sat]
  have run : ∀ {z}, z∈K4Core.sat s → K4Core.Reach 6 pool z := by
    intro z h
    exact step_reach c0 (step_reach c1 (step_reach c2 (step_reach c3
          (step_reach c4 (step_reach c5 (.done h))))))
  constructor
  · intro h
    apply no
    change endValue s = K4Core.tgt at h
    exact h ▸ run hz
  · intro h
    apply no
    change K4Core.neg (endValue s)=K4Core.tgt at h
    exact h ▸ run (K4Core.negmem hz)
end K4Six

namespace K4Six
theorem impossible (c0 c1 c2 c3 c4 c5 : Code) :
  let z := endValue (step c5 (step c4 (step c3 (step c2 (step c1 (step c0 pool))))))
  z≠target ∧ (~~~z)≠target :=
  fromSearch K4Num.allLower c0 c1 c2 c3 c4 c5
end K4Six

namespace OneNot10797.FourBridge
open K4Six
abbrev F := FreeAIG.Fn (Fin 4 → Bool)
def Represents (f : F) (v : T) := ∀ i : Fin 16, v.getLsbD i.val = f (fun j => i.val.testBit j.val)
theorem unique {f : F} {u v : T} (hu : Represents f u) (hv : Represents f v) : u=v :=
  BitVec.eq_of_getElem_eq (fun i hi => (hu ⟨i,hi⟩).trans (hv ⟨i,hi⟩).symm)
theorem negate {f v} (p : Represents f v) : Represents (FreeAIG.neg f) (~~~v) := by
  intro i
  rw [BitVec.getLsbD_not, p i]
  simp [FreeAIG.neg,i.isLt]
theorem both {a b u v} (p : Represents a u) (q : Represents b v) :
    Represents (FreeAIG.meet a b) (u &&& v) := by
  intro i
  rw [BitVec.getLsbD_and, p i, q i]
  rfl
theorem targetRep : Represents four target := by unfold Represents; decide +kernel
def SourceRep (S : Set F) (s : List T) := ∀ f ∈ S, ∃ w ∈ s, Represents f w
theorem initRep : SourceRep FreeAIG.Inputs pool := by
  rintro f ⟨i,rfl⟩
  have cert : ∀ j : Fin 4, (pool.getD j.val 0) ∈ pool ∧
      (∀ r : Fin 16, (pool.getD j.val 0).getLsbD r.val = r.val.testBit j.val) := by decide +kernel
  exact ⟨_, (cert i).1, (cert i).2⟩

theorem pickNat (n : Nat) (hn : n < 16) (s : List T) : pick (BitVec.ofNat 4 n) s = s.getD n 0 := by
  induction s generalizing n with
  | nil => simp [pick]
  | cons x xs ih =>
    cases n with
    | zero => rfl
    | succ n =>
      have cert : ∀ j : Fin 15, (BitVec.ofNat 4 (j.val+1))≠0 ∧
          (BitVec.ofNat 4 (j.val+1))-1=BitVec.ofNat 4 j.val := by decide +kernel
      obtain ⟨nz,pr⟩ := cert ⟨n,by omega⟩
      simp only at nz pr
      rw [pick, if_neg nz, pr, ih n (by omega), List.getD_cons_succ]

theorem availRep {S s f} (src : SourceRep S s) (sz : s.length ≤ 10) (h : FreeAIG.Avail S f) :
    ∃ (a : Addr) (n : Bool), Represents f (lit n (pick a s)) := by
  induction h with
  | src hm =>
    obtain ⟨v, hv, hr⟩ := src _ hm
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem hv
    refine ⟨BitVec.ofNat 4 i, false, ?_⟩
    rw [pickNat _ (by omega), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, e]
    exact hr
  | const b =>
    refine ⟨BitVec.ofNat 4 15,b,?_⟩
    rw [pickNat _ (by decide), List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    cases b <;> unfold Represents <;> decide +kernel
  | neg _ ih =>
    obtain ⟨a,n,r⟩ := ih
    refine ⟨a,!n,?_⟩
    have hh := negate r
    cases n <;> simpa [lit] using hh

def run (s : List T) : List Code → List T
  | [] => s
  | c::cs => run (step c s) cs

theorem trace {S t f} (h : FreeAIG.Has S t f) (s : List T) (src : SourceRep S s)
    (sz : s.length + t ≤ 10) :
    ∃ cs : List Code, cs.length ≤ t ∧ ∃ (a : Addr) (n : Bool), Represents f (lit n (pick a (run s cs))) := by
  induction h generalizing s with
  | done ha => exact ⟨[], Nat.zero_le _, availRep (s:=s) src (by omega) ha⟩
  | @step S k a b f ha hb _ ih =>
    obtain ⟨ia,na,ra⟩ := availRep src (by omega) ha
    obtain ⟨ib,nb,rb⟩ := availRep src (by omega) hb
    let c : Code := ⟨ia,ib,na,nb⟩
    have src' : SourceRep (insert (FreeAIG.meet a b) S) (step c s) := by
      rintro g (rfl|hs)
      · exact ⟨_,List.mem_cons_self, both ra rb⟩
      · obtain ⟨v,hv,r⟩ := src g hs
        exact ⟨v,List.mem_cons_of_mem _ hv,r⟩
    have bound : (step c s).length+k ≤ 10 := by simp [step]; omega
    obtain ⟨cs,ncs,r⟩ := ih _ src' bound
    exact ⟨c::cs, Nat.succ_le_succ ncs, r⟩
end OneNot10797.FourBridge

namespace OneNot10797.FourBridge
open K4Six
def Safe (v : T) := v≠target ∧ ~~~v≠target

theorem sixSafe (cs : List Code) (h : cs.length=6) : Safe (endValue (run pool cs)) := by
  rcases cs with _|⟨a,cs⟩ <;> simp only [List.length_nil, List.length_cons] at h
  · contradiction
  rcases cs with _|⟨b,cs⟩ <;> simp only [List.length_nil, List.length_cons] at h
  · contradiction
  rcases cs with _|⟨c,cs⟩ <;> simp only [List.length_nil, List.length_cons] at h
  · contradiction
  rcases cs with _|⟨d,cs⟩ <;> simp only [List.length_nil, List.length_cons] at h
  · contradiction
  rcases cs with _|⟨e,cs⟩ <;> simp only [List.length_nil, List.length_cons] at h
  · contradiction
  rcases cs with _|⟨f,cs⟩ <;> simp only [List.length_nil, List.length_cons] at h
  · contradiction
  have : cs.length=0 := by omega
  obtain rfl : cs=[] := List.length_eq_zero_iff.mp this
  exact impossible a b c d e f

theorem runAppend (s : List T) (a b : List Code) : run s (a++b) = run (run s a) b := by
  induction a generalizing s with
  | nil => rfl
  | cons c a ih => exact ih _

def dup : Code := ⟨0,0,false,false⟩
theorem dupHead (s : List T) : endValue (step dup s) = endValue s := by
  cases s <;> simp [endValue,step,dup,pick,lit]
theorem dupHeadN (s : List T) (n : Nat) : endValue (run s (List.replicate n dup)) = endValue s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ]; exact (ih _).trans (dupHead _)

theorem headSafe (cs : List Code) (h : cs.length≤6) : Safe (endValue (run pool cs)) := by
  have sz : (cs++List.replicate (6-cs.length) dup).length = 6 := by simp; omega
  have r := sixSafe _ sz
  rwa [runAppend,dupHeadN] at r

theorem memSafe (cs : List Code) (h : cs.length≤6) : ∀v∈run pool cs, Safe v := by
  induction cs using List.reverseRecOn with
  | nil =>
    intro v hv
    change v∈pool at hv
    simp only [pool,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl|rfl|rfl|rfl <;> unfold Safe <;> decide +kernel
  | append_singleton cs c ih =>
    have h' : cs.length ≤ 6 := by simp at h; omega
    intro v hv
    have hc := headSafe (cs++[c]) h
    rw [runAppend] at hv hc
    change v∈_ :: run pool cs at hv
    rcases List.mem_cons.mp hv with rfl|ht
    · exact hc
    · exact ih h' _ ht

theorem pickMem (a : Addr) (s : List T) : pick a s = 0 ∨ pick a s ∈ s := by
  induction s generalizing a with
  | nil => exact Or.inl rfl
  | cons x xs ih =>
    by_cases z : a=0
    · simp [pick,z]
    · rw [pick,if_neg z]
      rcases ih (a-1) with h|h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)

end OneNot10797.FourBridge
namespace OneNot10797
open K4Six FourBridge
theorem fourLower {t} (h : FreeAIG.Has FreeAIG.Inputs t four) : 7≤t := by
  by_contra! tooSmall
  have size : pool.length+t≤10 := by change 4+t≤10; omega
  obtain ⟨cs,len,a,n,r⟩ := trace h _ initRep size
  have eq := unique r targetRep
  have s : Safe (pick a (run pool cs)) := by
    rcases pickMem a (run pool cs) with z|m
    · rw [z]; unfold Safe; decide +kernel
    · exact memSafe _ (by omega) _ m
  cases n
  · exact s.1 eq
  · exact s.2 eq
end OneNot10797

namespace OneNot10797
open FreeAIG PEqualNP.CircuitLowerBounds
theorem positive (C : Circuit) (lg : ∀g∈C.gates,
    (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2) (sem : fits C) : Replacement C :=
  allNotReplacement (fun _ h=>fourLower h) triple C lg sem
end OneNot10797

end PEqualNP.Outside.L_meta_10796

theorem PEqualNP.Outside.L_meta_10796 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _ computes
  obtain ⟨D,hm,hs,hf⟩ := PEqualNP.Outside.L_meta_10796.OneNot10797.positive ⟨gates,o⟩ legal computes
  exact ⟨D.gates,D.output,hm,hs,hf⟩
