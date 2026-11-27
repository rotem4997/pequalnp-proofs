import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import PEqualNP.Defs

-- The seven-vertex signed certificate is adapted from L-meta-2960 (PR 5972).
-- The live-wire semantics and the monotone search are adapted from L-meta-1007.
-- Fixing any of the four degree-two vertices to zero leaves a seven-vertex
-- theta graph requiring eleven binary gates, even with free inversions.
-- With twelve gates available, each such vertex can only be consumed once,
-- in an OR, and every remaining gate must be binary.
namespace PEqualNP.Outside.L_meta_3143
namespace Theta

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A wire is a phase and a column of sampled truth values. Complementing a wire is free.
abbrev Wire := Bool × ℕ
def zero : Wire := (false,0)
def flip (a : Wire) : Wire := (!a.1,a.2)
def combine (d a b : ℕ) : ℕ :=
  match d with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)
def opIndex (a b : Bool) : ℕ :=
  if a then (if b then 1 else 3) else (if b then 2 else 0)
def meet (a b : Wire) : Wire := (a.1 && b.1,combine (opIndex a.1 b.1) a.2 b.2)
def join (a b : Wire) : Wire := flip (meet (flip a) (flip b))
def read (j : ℕ) (a : Wire) : Bool := a.1 != a.2.testBit j
lemma read_zero (j : ℕ) : read j zero=false := by simp [read,zero]
lemma read_flip (j : ℕ) (a : Wire) : read j (flip a)=!(read j a) := by
  cases a with | mk s a => cases s <;> cases h : a.testBit j <;> simp [read,flip,h]
lemma read_meet (j : ℕ) (a b : Wire) : read j (meet a b) = (read j a && read j b) := by
  obtain ⟨s,a⟩ := a;obtain ⟨t,b⟩ := b
  cases s <;> cases t <;> cases h : a.testBit j <;> cases g : b.testBit j <;>
    simp [read,meet,combine,opIndex,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,h,g]
lemma read_join (j : ℕ) (a b : Wire) : read j (join a b) = (read j a || read j b) := by
  simp only [join,read_flip,read_meet];cases read j a <;> cases read j b <;> rfl

def gate (w : List Wire) (g : Gate) : Wire :=
  let arg := fun i => w.getD i zero
  match g.op,g.inputs with
  | .not, xs => flip (arg (xs.headD w.length))
  | .and, [] => flip zero
  | .or, [] => zero
  | .and, [i] | .or, [i] => arg i
  | .and, i::j::_ => meet (arg i) (arg j)
  | .or, i::j::_ => join (arg i) (arg j)
  | _,_ => zero
def execute (gs : List Gate) (w : List Wire) : List Wire :=
  gs.foldl (fun w g => w++[gate w g]) w
def boolRun (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w++[g.op.eval (g.inputs.map fun i => w.getD i false)]) w
lemma read_get (j : ℕ) (w : List Wire) (i : ℕ) :
    (w.map (read j)).getD i false = read j (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases h : w[i]? with
  | none => exact (read_zero j).symm
  | some a => rfl
lemma gate_read (w : List Wire) (g : Gate) (legal : g.op ∈ ({.and,.or,.not} : Set GateOp) ∧ g.inputs.length ≤ 2) (j : ℕ) :
    read j (gate w g) = g.op.eval (g.inputs.map fun i => (w.map (read j)).getD i false) := by
  simp_rw [read_get]
  obtain ⟨op,xs⟩ := g
  obtain ⟨ops,len⟩ := legal
  change op ∈ ({.and,.or,.not} : Set GateOp) at ops
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ops
  rcases ops with rfl|rfl|rfl <;>
    rcases xs with _|⟨i,_|⟨k,_|⟨h,rest⟩⟩⟩ <;>
    simp_all [gate,GateOp.eval,read_flip,read_meet,read_join,read_get,read_zero,List.getD_eq_default]
lemma execute_read (j : ℕ) (gs : List Gate) (w : List Wire) (legal : ∀ g ∈ gs,
    g.op ∈ ({.and,.or,.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (execute gs w).map (read j) = boolRun gs (w.map (read j)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gate w g])).map (read j) = boolRun gs (_++[_])
    rw [ih _ (fun v hv => legal v (.tail _ hv))]
    simp [gate_read w g (legal g List.mem_cons_self) j]

def counted (g : Gate) : Bool := match g.op with | .not => false | _ => true
def reps (w : List Wire) := w.map Prod.snd
def simple (w : List Wire) (z : ℕ) := z=0 ∨ z∈reps w
def priced (w : List Wire) (paid : Bool) (z : ℕ) := simple w z ∨
    (paid = true ∧ ∃ d < 4, ∃ a ∈ reps w, ∃ b ∈ reps w, a≠0 ∧ b≠0 ∧ a≠b ∧ z=combine d a b)
lemma get_simple (w : List Wire) (i : ℕ) : simple w (w.getD i zero).2 := by
  simp only [List.getD_eq_getElem?_getD]
  cases eq : w[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (List.mem_map.mpr ⟨a,List.mem_of_getElem? eq,rfl⟩)
lemma combine_eq_cases (d a b : ℕ) (hd : d<4) (h : a=0 ∨ b=0 ∨ a=b) :
    combine d a b=0 ∨ combine d a b=a ∨ combine d a b=b := by
  rcases h with h|h|h <;> subst_vars <;> interval_cases d <;> simp [combine]
lemma made (w : List Wire) (d : ℕ) (a b : Wire) (hd : d<4) (pa : simple w a.2) (pb : simple w b.2) :
    priced w true (combine d a.2 b.2) := by
  by_cases h : a.2=0 ∨ b.2=0 ∨ a.2=b.2
  · rcases combine_eq_cases _ _ _ hd h with e|e|e
    · exact Or.inl (Or.inl e)
    · apply Or.inl; rw [e]; exact pa
    · apply Or.inl; rw [e]; exact pb
  · push Not at h
    exact Or.inr ⟨rfl,d,hd,a.2,pa.resolve_left h.1,b.2,pb.resolve_left h.2.1,h.1,h.2.1,h.2.2,rfl⟩
lemma op_lt (s t : Bool) : opIndex s t < 4 := by cases s <;> cases t <;> decide
lemma gate_priced (w : List Wire) (g : Gate) : priced w (counted g) (gate w g).2 := by
  obtain ⟨op,xs⟩ := g
  cases op with
  | and =>
    rcases xs with _|⟨i,_|⟨j,t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made w _ _ _ (op_lt _ _) (get_simple w i) (get_simple w j)
  | or =>
    rcases xs with _|⟨i,_|⟨j,t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made w _ _ _ (op_lt _ _) (get_simple w i) (get_simple w j)
  | mod _ | maj => exact Or.inl (Or.inl rfl)
  | _ => exact Or.inl (get_simple w _)

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def Good (m a : ℕ) := ∀ i<m, a.testBit i ≠ a.testBit (m+i)

inductive Live (m : ℕ) : ℕ → Finset ℕ → Prop
  | done {a} (hg : Good m a) (nonzero : a≠0) : Live m 0 {a}
  | step {k U a b d} (hd : d<4) (ha : a≠0) (hb : b≠0) (diff : a≠b)
      (fresh : combine d a b ∉ insert a (insert b U))
      (next : Live m k (insert (combine d a b) U)) :
      Live m (k+1) (insert a (insert b U))

lemma liveNonzero {m k S} (h : Live m k S) : ∀ a∈S,a≠0 := by
  induction h with
  | done hg hn => simpa using hn
  | @step k U a b d hd ha hb ne fresh tail ih =>
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact ha
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact hb
    exact ih x (Finset.mem_insert_of_mem hx)
lemma liveSize {m k S} (h : Live m k S) : S.card≤k+1 := by
  induction h with
  | done hg hn => simp
  | @step k U a b d hd ha hb ne fresh tail ih =>
    have z : combine d a b ∉ U := fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    rw [Finset.card_insert_of_notMem z] at ih
    have u := Finset.card_insert_le a (insert b U)
    have v := Finset.card_insert_le b U
    omega
lemma combine_congr_bits (d a b i j : ℕ) (p : a.testBit i=a.testBit j) (q : b.testBit i=b.testBit j) :
    (combine d a b).testBit i=(combine d a b).testBit j := by
  rcases d with _|(_|(_|d)) <;> simp [combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,p,q]
lemma liveSeparates {m k S} (h : Live m k S) (i : ℕ) (hi : i<m) :
    ∃ a∈S,a.testBit i≠a.testBit (m+i) := by
  induction h with
  | done hg hn => exact ⟨_,Finset.mem_singleton_self _,hg i hi⟩
  | @step k U a b d hd ha hb ne fresh tail ih =>
    obtain ⟨x,hx,dist⟩ := ih
    rcases Finset.mem_insert.mp hx with rfl|hx
    · by_cases v : a.testBit i=a.testBit (m+i)
      · exact ⟨b,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),fun u => dist (combine_congr_bits _ _ _ _ _ v u)⟩
      · exact ⟨a,Finset.mem_insert_self _ _,v⟩
    · exact ⟨x,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx),dist⟩

lemma pull {m k S w z p} (h : Live m k S) (op : priced w p z)
    (sub : ∀ a∈S, a∈reps w ++ [z]) :
    ∃ l T, l ≤ k + p.toNat ∧ Live m l T ∧ ∀ a∈T, a∈reps w := by
  by_cases needed : z∈S
  · by_cases available : z∈reps w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a∈reps w ∨ a=z) with old|rfl
      · exact old
      · exact available
    · rcases op with easy|⟨rfl,d,hd,a,xa,b,xb,na,nb,ab,rfl⟩
      · rcases easy with e|e
        · exact ((liveNonzero h z needed) e).elim
        · exact (available e).elim
      · let g := combine d a b
        let U := S.erase g
        have tail : Live m k (insert g U) := by change Live m k (insert g (S.erase g)); rw [Finset.insert_erase (show g∈S from needed)]; exact h
        have old (x : ℕ) (hx : x∈U) : x∈reps w := by
          obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hx
          have h' : x∈reps w ∨ x=g := by simpa using sub x mem
          exact h'.resolve_right ne
        have fresh : g ∉ insert a (insert b U) := by
          intro eq
          rcases Finset.mem_insert.mp eq with e|h'
          · exact available (show g∈reps w by rw [e];exact xa)
          rcases Finset.mem_insert.mp h' with e|u
          · exact available (show g∈reps w by rw [e];exact xb)
          · exact available (old _ u)
        refine ⟨k+1,insert a (insert b U),by simp,Live.step hd na nb ab fresh tail,?_⟩
        simpa using And.intro xa (And.intro xb old)
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have ne : a≠z := fun e => needed (e ▸ ha)
    simpa [ne] using sub a ha

lemma extract {m out} (hg : Good m out) (hn : out≠0) (gs : List Gate) (w : List Wire)
    (found : out∈reps (execute gs w)) :
    ∃ k S, k≤gs.countP counted ∧ Live m k S ∧ ∀ a∈S, a∈reps w := by
  induction gs generalizing w with
  | nil => exact ⟨0,{out},by simp,Live.done hg hn,by simpa [execute] using found⟩
  | cons g gs ih =>
    obtain ⟨k,S,lim,h,sub⟩ := ih (w++[gate w g]) found
    have sub' : ∀ a∈S,a∈reps w ++ [(gate w g).2] := by simpa [reps] using sub
    obtain ⟨l,T,cost,ht,raw⟩ := pull h (gate_priced w g) sub'
    refine ⟨l,T,?_,ht,raw⟩
    cases e : counted g <;> simp [e,Bool.toNat] at cost ⊢ <;> omega

def separation (m a : ℕ) := a ^^^ (a >>> m)
def cover (m : ℕ) : List ℕ → ℕ
  | [] => 0
  | a::t => separation m a ||| cover m t
def full (m : ℕ) := (1 <<< m)-1
def enough (m c : ℕ) := (c &&& full m) == full m
lemma coverBit (m i : ℕ) (v : List ℕ) : (cover m v).testBit i=true ↔
    ∃ a∈v,a.testBit i≠a.testBit (m+i) := by
  induction v with
  | nil => simp [cover]
  | cons a t ih =>
    simp only [cover,Nat.testBit_or,Bool.or_eq_true,ih,List.mem_cons,separation,Nat.testBit_xor,Nat.testBit_shiftRight]
    cases v1 : a.testBit i <;> cases v2 : a.testBit (m+i) <;> simp [v1,v2] <;> aesop
lemma enoughLive {m k S} (h : Live m k S) (v : List ℕ) (rep : v.toFinset=S) : enough m (cover m v)=true := by
  apply beq_iff_eq.mpr
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  have bit : (full m).testBit i=decide (i<m) := by simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]
  by_cases hi : i<m
  · have ⟨x,hx,good⟩ := liveSeparates h i hi
    have xc : x∈v := List.mem_toFinset.mp (rep ▸ hx)
    have mark := (coverBit m i v).2 ⟨x,xc,good⟩
    simp [mark,bit,hi]
  · simp [bit,hi]

def save (keep : Bool) (a : ℕ) (rest : List ℕ) := if keep then a::rest else rest
def without (v : List ℕ) (a b : ℕ) := v.filter (fun x => x != a && x != b)
def optionStep (m fuel : ℕ) (go : List ℕ → Bool) (rest : List ℕ) (n cv a b z : ℕ) (ka kb : Bool) : Bool :=
  let len := 1+n+ka.toNat+kb.toNat
  len ≤ fuel+1 && enough m (((separation m z ||| cv) ||| (if ka then separation m a else 0)) |||
    (if kb then separation m b else 0)) && go (z::save ka a (save kb b rest))
def gateStep (m fuel : ℕ) (go : List ℕ → Bool) (v rest : List ℕ) (n cv a b z : ℕ) : Bool :=
  z != 0 && !(v.contains z) &&
  (optionStep m fuel go rest n cv a b z false false || optionStep m fuel go rest n cv a b z true false ||
   optionStep m fuel go rest n cv a b z false true || optionStep m fuel go rest n cv a b z true true)
def pairStep (m fuel : ℕ) (go : List ℕ → Bool) (v : List ℕ) (a b : ℕ) : Bool :=
  if a<b then
    let rest := without v a b
    let check := gateStep m fuel go v rest rest.length (cover m rest) a b
    check (a &&& b) || check (a ||| b) || check (a ^^^ (a &&& b)) || check (b ^^^ (a &&& b))
  else false
def anyGate (m fuel : ℕ) (go : List ℕ → Bool) (v : List ℕ) : Bool :=
  v.any (fun a => v.any (fun b => pairStep m fuel go v a b))
def terminal (m : ℕ) (v : List ℕ) := v.any (fun a => enough m (separation m a))
def search (m : ℕ) : ℕ → List ℕ → Bool
  | 0, v => terminal m v
  | fuel+1, v => terminal m v || anyGate m fuel (search m fuel) v

lemma surface (m a i : ℕ) : (separation m a).testBit i=true ↔ a.testBit i≠a.testBit (m+i) := by
  simp only [separation,Nat.testBit_xor,Nat.testBit_shiftRight]
  cases a.testBit i <;> cases a.testBit (m+i) <;> decide
lemma ends {m a} (h : Good m a) (v : List ℕ) (mem : a∈v) : terminal m v=true := by
  apply List.any_eq_true.mpr;refine ⟨a,mem,?_⟩
  apply beq_iff_eq.mpr;apply Nat.eq_of_testBit_eq;intro i;rw [Nat.testBit_and]
  have e : (full m).testBit i=decide (i<m) := by simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]
  by_cases l : i<m
  · simp [e,l,(surface _ _ _).2 (h i l)]
  · simp [e,l]
lemma option_ok {m fuel go rest a b z ka kb} (lim : (z::save ka a (save kb b rest)).length≤fuel+1)
    (cov : enough m (cover m (z::save ka a (save kb b rest)))=true)
    (next : go (z::save ka a (save kb b rest))=true) :
    optionStep m fuel go rest rest.length (cover m rest) a b z ka kb=true := by
  have size : 1+rest.length+ka.toNat+kb.toNat≤fuel+1 := by
    cases ka <;> cases kb <;> simp [save,Bool.toNat] at lim ⊢ <;> omega
  have eq : enough m (((separation m z ||| cover m rest) ||| (if ka then separation m a else 0)) ||| (if kb then separation m b else 0))=true := by
    cases ka <;> cases kb <;> simpa [save,cover,Nat.or_assoc,Nat.or_left_comm,Nat.or_comm] using cov
  simp [optionStep,size,eq,next]
lemma gate_ok {m fuel go v rest n cv a b z ka kb} (nz : z≠0) (fresh : z∉v)
    (which : optionStep m fuel go rest n cv a b z ka kb=true) :
    gateStep m fuel go v rest n cv a b z=true := by
  cases ka <;> cases kb <;> simp [gateStep,nz,fresh,which]
lemma pair_ok {m fuel go v a b d} (ordered : a<b) (hd : d<4)
    (step : let rest := without v a b;gateStep m fuel go v rest rest.length (cover m rest) a b (combine d a b)=true) :
    pairStep m fuel go v a b=true := by
  interval_cases d <;> simp only [combine] at step <;> simp [pairStep,ordered,step]
lemma swapOp (d a b : ℕ) (hd : d<4) : ∃ e<4,combine d a b=combine e b a := by
  interval_cases d
  · exact ⟨0,by decide,Nat.and_comm a b⟩
  · exact ⟨1,by decide,Nat.or_comm a b⟩
  · exact ⟨3,by decide,by simp [combine,Nat.and_comm]⟩
  · exact ⟨2,by decide,by simp [combine,Nat.and_comm]⟩
lemma listNext {v : List ℕ} {a b z : ℕ} {U : Finset ℕ} (rep : v.toFinset=insert a (insert b U))
    (ab : a≠b) (fz : z∉insert a (insert b U)) (nd : v.Nodup) :
    let rest := without v a b
    let next := z::save (decide (a∈U)) a (save (decide (b∈U)) b rest)
    next.toFinset=insert z U ∧ next.Nodup := by
  dsimp only
  have mem (x : ℕ) : x∈without v a b ↔ x∈U ∧ x≠a ∧ x≠b := by
    simp only [without,List.mem_filter,Bool.and_eq_true,bne_iff_ne]
    have e : x∈v ↔ x=a ∨ x=b ∨ x∈U := by rw [← List.mem_toFinset,rep];simp
    tauto
  have nr := nd.filter (fun x => x != a && x != b)
  change (without v a b).Nodup at nr
  have md (x : ℕ) : (x∈save (decide (a∈U)) a (save (decide (b∈U)) b (without v a b))) ↔ x∈U := by
    by_cases xa : x=a
    · subst x; by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,mem,ab]
    by_cases xb : x=b
    · subst x; by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,mem,Ne.symm ab]
    by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,mem,xa,xb]
  constructor
  · ext x;simp [md]
  · simp only [List.nodup_cons,md]
    refine ⟨fun m => fz (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m)),?_⟩
    have an : a∉without v a b := fun x => (mem _).1 x |>.2.1 rfl
    have bn : b∉without v a b := fun x => (mem _).1 x |>.2.2 rfl
    by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,nr,ab,an,bn]
lemma orderedStep {m fuel n U a b d v} {go : List ℕ→Bool} (hd : d<4)
    (lt : a<b) (nz : combine d a b≠0) (fresh : combine d a b∉insert a (insert b U))
    (rep : List.toFinset v=insert a (insert b U)) (nd : v.Nodup) (lim : n≤fuel)
    (tail : Live m n (insert (combine d a b) U))
    (nextOK : ∀ v : List ℕ, v.toFinset=insert (combine d a b) U → v.Nodup → go v=true) :
    pairStep m fuel go v a b=true := by
  let z := combine d a b
  let rest := without v a b
  let next := z::save (decide (a∈U)) a (save (decide (b∈U)) b rest)
  obtain ⟨r,nu⟩ := listNext (z:=z) rep (Nat.ne_of_lt lt) fresh nd
  have small := liveSize tail
  change (insert z U).card≤n+1 at small
  have length : next.length=(insert z U).card := by rw [←r,List.toFinset_card_of_nodup nu]
  have bound : next.length≤fuel+1 := by omega
  have coverOK := enoughLive tail next r
  have ok := option_ok bound coverOK (nextOK next r nu)
  apply pair_ok lt hd
  exact gate_ok nz (fun h => fresh (rep ▸ List.mem_toFinset.mpr h)) ok
lemma transition {m fuel n U a b d v} {go : List ℕ→Bool} (hd : d<4)
    (ab : a≠b) (fresh : combine d a b∉insert a (insert b U))
    (rep : List.toFinset v=insert a (insert b U)) (nd : v.Nodup) (lim : n≤fuel)
    (tail : Live m n (insert (combine d a b) U))
    (nextOK : ∀ v : List ℕ, v.toFinset=insert (combine d a b) U → v.Nodup → go v=true) :
    anyGate m fuel go v=true := by
  have ma : a∈v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_self _ _)
  have mb : b∈v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have nz := liveNonzero tail _ (Finset.mem_insert_self _ _)
  rcases lt_or_gt_of_ne ab with lt|gt
  · exact List.any_eq_true.mpr ⟨a,ma,List.any_eq_true.mpr ⟨b,mb,orderedStep hd lt nz fresh rep nd lim tail nextOK⟩⟩
  · obtain ⟨e,he,eq⟩ := swapOp d a b hd
    have rev : insert a (insert b U)=insert b (insert a U) := Finset.insert_comm a b U
    rw [rev] at fresh rep
    rw [eq] at fresh nz tail nextOK
    exact List.any_eq_true.mpr ⟨b,mb,List.any_eq_true.mpr ⟨a,ma,orderedStep he gt nz fresh rep nd lim tail nextOK⟩⟩

theorem complete (m fuel : ℕ) {n S} (h : Live m n S) (lim : n≤fuel)
    (v : List ℕ) (rep : v.toFinset=S) (nd : v.Nodup) : search m fuel v=true := by
  induction fuel generalizing n S v with
  | zero =>
    cases h with
    | done hg hn => exact ends hg v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self _))
    | step hd _ _ _ _ _ => omega
  | succ k ih =>
    rw [search,Bool.or_eq_true]
    cases h with
    | done hg hn => exact Or.inl (ends hg v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self _)))
    | step hd _ _ ab fresh tail =>
      exact Or.inr (transition hd ab fresh rep nd (by omega) tail (fun v hv nv => ih tail (by omega) v hv nv))

structure Projection (m h : ℕ) where
  toFun : ℕ → ℕ
  atZero : toFun 0=0
  combineEq : ∀ d a b, d<4 → toFun (combine d a b)=combine d (toFun a) (toFun b)
  good : ∀ a, Good m a → Good h (toFun a)
  someRow : 0<h

def Possible (m k : ℕ) (av : List ℕ) :=
  ∃ j S, j≤k ∧ Live m j S ∧ ∀ x∈S,x∈av
def charge (av : List ℕ) (z : ℕ) := z != 0 && !(av.contains z)
lemma pullPaid {m k d a b : ℕ} {av : List ℕ} (hd : d<4) (ha : a∈av) (hb : b∈av)
    (later : Possible m k (av++[combine d a b])) :
    Possible m (k+(charge av (combine d a b)).toNat) av := by
  let w := av.map (fun x => (false,x))
  have repr : reps w=av := by simp [w,reps,List.map_map,Function.comp_def]
  obtain ⟨j,S,lim,live,sub⟩ := later
  have needed : ∀ x∈S,x∈reps w++[combine d a b] := by simpa [repr] using sub
  have price : priced w (charge av (combine d a b)) (combine d a b) := by
    by_cases nz : combine d a b=0
    · exact Or.inl (Or.inl nz)
    by_cases old : combine d a b∈av
    · exact Or.inl (Or.inr (repr ▸ old))
    have paid : charge av (combine d a b)=true := by simp [charge,nz,old]
    have special : ¬(a=0 ∨ b=0 ∨ a=b) := by
      intro h
      rcases combine_eq_cases _ _ _ hd h with zero|rfl'|rfl'
      · exact nz zero
      · exact old (by rw [rfl'];exact ha)
      · exact old (by rw [rfl'];exact hb)
    exact Or.inr ⟨paid,d,hd,a,repr ▸ ha,b,repr ▸ hb,
      fun x => special (Or.inl x),fun x => special (Or.inr (Or.inl x)),fun x => special (Or.inr (Or.inr x)),rfl⟩
  obtain ⟨l,T,le,ok,sub'⟩ := pull live price needed
  exact ⟨l,T,by omega,ok,by simpa [repr] using sub'⟩

def dead (p : ℕ→ℕ) (S : Finset ℕ) := (S.filter (fun x => p x=0)).card
lemma deadStay {p : ℕ→ℕ} {a : ℕ} {S : Finset ℕ} (h : p a≠0) : dead p (insert a S)=dead p S := by
  simp [dead,Finset.filter_insert,h]
lemma deadLimit (p : ℕ→ℕ) (a : ℕ) (S : Finset ℕ) : dead p (insert a S)≤dead p S+1 := by
  by_cases x : p a=0
  · simpa [dead,Finset.filter_insert,x] using Finset.card_insert_le a (S.filter (fun x => p x=0))
  · simp [deadStay x]
lemma deadMono (p : ℕ→ℕ) (a : ℕ) (S : Finset ℕ) : dead p S ≤ dead p (insert a S) := by
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
lemma deadGrow {p : ℕ→ℕ} {a : ℕ} {S : Finset ℕ} (z : p a=0) (fresh : a∉S) :
    dead p (insert a S)=dead p S+1 := by
  have nf : a∉S.filter (fun x => p x=0) := fun h => fresh (Finset.mem_filter.mp h).1
  simp [dead,Finset.filter_insert,z,Finset.card_insert_of_notMem nf]
lemma countCharge {m h d a b : ℕ} (p : Projection m h) (hd : d<4) (U : Finset ℕ)
    (fz : combine d a b∉insert a (insert b U)) (av : List ℕ) (ma : p.toFun a∈av) (mb : p.toFun b∈av) :
    (charge av (p.toFun (combine d a b))).toNat + dead p.toFun (insert a (insert b U)) ≤
      1+dead p.toFun (insert (combine d a b) U) := by
  have up := deadMono p.toFun (combine d a b) U
  have la := deadLimit p.toFun a (insert b U)
  have lb := deadLimit p.toFun b U
  have free (bad : p.toFun a=0 ∨ p.toFun b=0) : charge av (p.toFun (combine d a b))=false := by
    rw [p.combineEq _ _ _ hd]
    rcases combine_eq_cases _ _ _ hd (bad.imp_right Or.inl) with e|e|e <;> simp [charge,e,ma,mb]
  by_cases az : p.toFun a=0
  · rw [free (Or.inl az)];simp only [Bool.toNat_false,Nat.zero_add]
    by_cases bz : p.toFun b=0
    · have zz : p.toFun (combine d a b)=0 := by
        rw [p.combineEq _ _ _ hd,az,bz];interval_cases d <;> decide
      have fresh : combine d a b∉U := fun m => fz (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
      rw [deadGrow zz fresh];omega
    · rw [deadStay bz] at la;omega
  · rw [deadStay az]
    by_cases bz : p.toFun b=0
    · rw [free (Or.inr bz)];simp only [Bool.toNat_false,Nat.zero_add];omega
    · rw [deadStay bz];cases charge av (p.toFun (combine d a b)) <;> simp [Bool.toNat] <;> omega

theorem projectLive {m h k S} (p : Projection m h) (live : Live m k S) :
    ∃ j T,j+dead p.toFun S≤k ∧ Live h j T ∧ ∀ x∈T,x∈S.image p.toFun := by
  induction live with
  | @done a hg hn =>
    have gp := p.good a hg
    have nz : p.toFun a≠0 := by intro e;have x := gp 0 p.someRow;simp [e] at x
    exact ⟨0,{p.toFun a},by simp [dead,nz],Live.done gp nz,by simp⟩
  | @step k U a b d hd ha hb ab fz tail ih =>
    obtain ⟨j,T,cost,ok,raw⟩ := ih
    let av := ((insert a (insert b U)).image p.toFun).toList
    have ma : p.toFun a∈av := by simp [av]
    have mb : p.toFun b∈av := by simp [av]
    have later : Possible h j (av++[combine d (p.toFun a) (p.toFun b)]) := by
      refine ⟨j,T,le_rfl,ok,?_⟩
      intro z hz
      have has := raw _ hz
      simp only [Finset.image_insert,Finset.mem_insert] at has
      rcases has with rfl|old
      · simp [p.combineEq d a b hd]
      · have inav : z∈av := by simpa [av] using (Or.inr (Or.inr old) : z=p.toFun a ∨ z=p.toFun b ∨ z∈U.image p.toFun)
        simp [inav]
    obtain ⟨l,V,lim,good,sub⟩ := pullPaid hd ma mb later
    rw [←p.combineEq d a b hd] at lim
    have bound := countCharge p hd U fz av ma mb
    exact ⟨l,V,by omega,good,by simpa [av] using sub⟩

lemma full_bit (m i : ℕ) : (full m).testBit i=decide (i<m) := by
  simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]

def half (m q r a : ℕ) := (a &&& q &&& full m) |||
    (if a.testBit r then ((full m ^^^ q) &&& full m) else 0)
def slice (m q r a : ℕ) := half m q r a ||| ((half m q r (a >>> m)) <<< m)
lemma half_bit (m q r a i : ℕ) : (half m q r a).testBit i =
    (decide (i<m) && (if q.testBit i then a.testBit i else a.testBit r)) := by
  cases e : a.testBit r <;> cases f : q.testBit i <;> by_cases l : i<m <;>
    simp [half,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,full_bit,e,f,l]
lemma slice_lo {m i : ℕ} (q r a : ℕ) (hi : i<m) : (slice m q r a).testBit i =
    a.testBit (if q.testBit i then i else r) := by
  cases e : q.testBit i <;> simp [slice,Nat.testBit_or,Nat.testBit_shiftLeft,half_bit,hi,e,(show ¬ (m ≤ i) from by omega)]
lemma slice_hi {m i : ℕ} (q r a : ℕ) (hi : i<m) : (slice m q r a).testBit (m+i) =
    a.testBit (m+(if q.testBit i then i else r)) := by
  have n : ¬ (m + i < m) := by omega
  cases e : q.testBit i <;> simp [slice,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_shiftRight,half_bit,hi,e,n]
lemma slice_above {m i : ℕ} (q r a : ℕ) (hi : 2 * m ≤ i) : (slice m q r a).testBit i=false := by
  simp [slice,Nat.testBit_or,Nat.testBit_shiftLeft,half_bit,(show ¬ (i < m) from by omega),(show ¬ (i - m < m) from by omega)]
lemma slice_hom (m q r d a b : ℕ) (hd : d<4) : slice m q r (combine d a b)=combine d (slice m q r a) (slice m q r b) := by
  apply Nat.eq_of_testBit_eq;intro i
  by_cases lo : i<m
  · rw [slice_lo _ _ _ lo]
    interval_cases d <;> simp [combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,slice_lo _ _ _ lo]
  by_cases upper : i<2*m
  · let j := i-m
    have h : j<m := by dsimp [j];omega
    have e : i=m+j := by dsimp [j];omega
    rw [e,slice_hi _ _ _ h]
    interval_cases d <;> simp [combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,slice_hi _ _ _ h]
  · have large := slice_above (m:=m) (i:=i) (hi := (show 2 * m ≤ i from by omega))
    interval_cases d <;> simp [combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,large]
def projection (m q r : ℕ) (hr : r<m) : Projection m m where
  toFun := slice m q r
  atZero := by simp [slice,half]
  combineEq := slice_hom m q r
  good := by
    intro a ga i hi
    rw [slice_lo _ _ _ hi,slice_hi _ _ _ hi]
    cases q.testBit i
    · exact ga r hr
    · exact ga i hi
  someRow := by omega

lemma enoughSup {m k S} (h : Live m k S) (v : List ℕ) (sub : ∀ x∈S,x∈v) : enough m (cover m v)=true := by
  apply beq_iff_eq.mpr;apply Nat.eq_of_testBit_eq;intro i
  rw [Nat.testBit_and,full_bit]
  by_cases hi : i<m
  · obtain ⟨x,hx,g⟩ := liveSeparates h i hi
    have bit := (coverBit m i v).2 ⟨x,sub _ hx,g⟩
    simp [bit,hi]
  · simp [hi]
def start (m fuel : ℕ) (av : List ℕ) :=
  let v := av.eraseDups.filter (fun x => x != 0)
  let needed := fun a => !(enough m (cover m (v.filter (fun x => x != a))))
  let must := v.filter needed
  let extra := v.filter (fun x => !needed x)
  extra.sublists.any (fun t =>
    let s := (must++t).dedup
    s.length≤fuel+1 && enough m (cover m s) && search m fuel s)

theorem start_complete {m k S} (h : Live m k S) (av : List ℕ) (sub : ∀ x∈S,x∈av)
    (fuel : ℕ) (lim : k≤fuel) : start m fuel av=true := by
  let v := av.eraseDups.filter (fun x => x != 0)
  let needed := fun a => !(enough m (cover m (v.filter (fun x => x != a))))
  let must := v.filter needed
  let extra := v.filter (fun x => !needed x)
  let t := extra.filter (fun x => decide (x∈S))
  let s := (must++t).dedup
  have inV (x : ℕ) (hx : x∈S) : x∈v := by simp [v,sub x hx,liveNonzero h x hx]
  have fixed (a : ℕ) (ha : a∈must) : a∈S := by
    by_contra absent
    have no := (List.mem_filter.mp ha).2
    have all (x : ℕ) (hx : x∈S) : x∈v.filter (fun y => y != a) := by
      have ne : x≠a := by rintro rfl;exact absent hx
      simp [inV x hx,ne]
    have yes := enoughSup h _ all
    simpa [needed,yes] using no
  have eq : s.toFinset=S := by
    ext x
    constructor
    · intro mem
      have e : x∈must ∨ x∈t := by simpa [s] using mem
      rcases e with l|r
      · exact fixed x l
      · simpa using (List.mem_filter.mp r).2
    · intro mem
      have raw := inV x mem
      cases H : needed x <;> simp [s,must,t,extra,H,raw,mem]
  have nd : s.Nodup := List.nodup_dedup _
  have size : s.length≤fuel+1 := by
    have vsize := liveSize h
    rw [←eq,List.toFinset_card_of_nodup nd] at vsize;omega
  have test := complete m fuel h lim s eq nd
  have cov := enoughLive h s eq
  apply List.any_eq_true.mpr
  refine ⟨t,List.mem_sublists.mpr (List.filter_sublist),?_⟩
  change (decide (s.length≤fuel+1) && enough m (cover m s) && search m fuel s)=true
  simp [size,cov,test]

def cutSearch (m q fuel : ℕ) (v : List ℕ) : Bool :=
  let r := min (Nat.log2 q) (m-1)
  let xs := v.map (slice m q r)
  let gone := xs.count 0
  gone≤fuel && start m (fuel-gone) xs

theorem cut_complete {m k S} (hm : 0<m) (h : Live m k S) (v : List ℕ) (rep : v.toFinset=S) (nd : v.Nodup)
    (q fuel : ℕ) (lim : k≤fuel) : cutSearch m q fuel v=true := by
  let r := min (Nat.log2 q) (m-1)
  let p := projection m q r (show r<m by dsimp [r];omega)
  obtain ⟨l,T,cost,live,sub⟩ := projectLive p h
  let xs := v.map (slice m q r)
  have fixed : dead p.toFun S=xs.count 0 := by
    rw [←rep];dsimp [dead]
    have E : v.toFinset.filter (fun x => p.toFun x=0) = (v.filter (fun x => decide (p.toFun x=0))).toFinset := by ext x;simp
    rw [E,List.toFinset_card_of_nodup (nd.filter _)]
    simp only [xs,List.count_eq_countP,List.countP_map,p,projection,Function.comp_apply]
    rw [List.countP_eq_length_filter]
    congr 2
  rw [fixed] at cost
  have has (x : ℕ) (hx : x∈T) : x∈xs := by simpa [xs,p,projection,←rep] using sub x hx
  have test := start_complete live xs has (fuel-xs.count 0) (by omega)
  change (decide (xs.count 0≤fuel) && start m (fuel-xs.count 0) xs)=true
  simp [test,show xs.count 0≤fuel by omega]

def oneOutput (m fuel : ℕ) (rest : List ℕ) (n cv a b z : ℕ) (ka kb : Bool) : List (List ℕ) :=
  if optionStep m fuel (fun _ => true) rest n cv a b z ka kb then [z::save ka a (save kb b rest)] else []
def oneGate (m fuel : ℕ) (v rest : List ℕ) (n cv a b z : ℕ) :=
  if z != 0 && !(v.contains z) then
    oneOutput m fuel rest n cv a b z false false ++ oneOutput m fuel rest n cv a b z true false ++
    oneOutput m fuel rest n cv a b z false true ++ oneOutput m fuel rest n cv a b z true true
  else []
def onePair (m fuel : ℕ) (v : List ℕ) (a b : ℕ) :=
  if a<b then
    let rest := without v a b
    let gate := oneGate m fuel v rest rest.length (cover m rest) a b
    gate (a &&& b) ++ gate (a ||| b) ++ gate (a ^^^ (a &&& b)) ++ gate (b ^^^ (a &&& b))
  else []
def successors (m fuel : ℕ) (v : List ℕ) :=
  v.flatMap (fun a => v.flatMap (fun b => onePair m fuel v a b))
lemma output_any (m fuel : ℕ) (go : List ℕ→Bool) (rest : List ℕ) (n cv a b z : ℕ) (ka kb : Bool) :
    (oneOutput m fuel rest n cv a b z ka kb).any go=optionStep m fuel go rest n cv a b z ka kb := by
  have E (t : Bool) (x : List ℕ) : ((if t then [x] else []) : List (List ℕ)).any go = (t && go x) := by cases t <;> simp
  unfold oneOutput
  rw [E]
  simp only [optionStep,Bool.and_true]
lemma gate_any (m fuel : ℕ) (go : List ℕ→Bool) (v rest : List ℕ) (n cv a b z : ℕ) :
    (oneGate m fuel v rest n cv a b z).any go=gateStep m fuel go v rest n cv a b z := by
  have E (t : Bool) (xs : List (List ℕ)) : (if t then xs else []).any go = (t && xs.any go) := by cases t <;> simp
  unfold oneGate gateStep
  rw [E]
  simp only [List.any_append,output_any,Bool.or_assoc,Bool.and_assoc]
lemma pair_any (m fuel : ℕ) (go : List ℕ→Bool) (v : List ℕ) (a b : ℕ) :
    (onePair m fuel v a b).any go=pairStep m fuel go v a b := by
  by_cases h : a<b <;> simp [onePair,pairStep,h,gate_any,Bool.or_assoc]
lemma successors_any (m fuel : ℕ) (go : List ℕ→Bool) (v : List ℕ) :
    (successors m fuel v).any go=anyGate m fuel go v := by simp [successors,anyGate,pair_any]
def feasible (m fuel : ℕ) (v : List ℕ) := ∃ k≤fuel,Live m k v.toFinset ∧ v.Nodup
theorem move {m fuel : ℕ} {v : List ℕ} (h : feasible m (fuel+1) v) :
    terminal m v=true ∨ ∃ w∈successors m fuel v,feasible m fuel w := by
  classical
  obtain ⟨k,lim,live,nd⟩ := h
  generalize e : v.toFinset=S at live
  cases live with
  | done hg hn => exact Or.inl (ends hg v (List.mem_toFinset.mp (e ▸ Finset.mem_singleton_self _)))
  | step hd ha hb ab fz tail =>
    let step := fun w => decide (feasible m fuel w)
    have hit := transition (go:=step) hd ab fz e nd (by omega : _≤fuel) tail (fun w rep nu => by
      apply decide_eq_true;exact ⟨_,by omega,rep ▸ tail,nu⟩)
    rw [←successors_any] at hit
    obtain ⟨w,hw,works⟩ := List.any_eq_true.mp hit
    exact Or.inr ⟨w,hw,of_decide_eq_true works⟩

def zeroPairs (m : ℕ) : List ℕ → ℕ → ℕ → ℕ
  | [], _, acc => acc
  | x::xs, code, acc => zeroPairs m xs (code >>> 1)
      (if code % 2=1 then acc ^^^ (acc &&& (x ||| (x >>> m))) else acc)

def flipSwap (i j a : ℕ) := if a.testBit i = a.testBit j then a else a ^^^ ((1 <<< i) ||| (1 <<< j))
lemma swapBit (i j k a : ℕ) : (flipSwap i j a).testBit k =
    a.testBit (if k=i then j else if k=j then i else k) := by
  by_cases h : a.testBit i=a.testBit j
  · by_cases x : k=i <;> by_cases y : k=j <;> simp [flipSwap,h,x,y] <;> grind
  · have n : i≠j := fun e => h (e ▸ rfl)
    by_cases x : k=i
    · subst k
      cases p : a.testBit i <;> cases q : a.testBit j <;>
        simp_all [flipSwap,Nat.testBit_xor,Nat.testBit_or,Nat.shiftLeft_eq,Nat.testBit_two_pow]
    by_cases y : k=j
    · subst k
      cases p : a.testBit i <;> cases q : a.testBit j <;>
        simp_all [flipSwap,Nat.testBit_xor,Nat.testBit_or,Nat.shiftLeft_eq,Nat.testBit_two_pow]
    · simp [flipSwap,h,x,y,Nat.testBit_xor,Nat.testBit_or,Nat.shiftLeft_eq,Nat.testBit_two_pow,Ne.symm x,Ne.symm y]
lemma flipSwap_twice (i j a : ℕ) : flipSwap i j (flipSwap i j a)=a := by
  apply Nat.eq_of_testBit_eq;intro k
  by_cases x : k=i <;> by_cases y : k=j <;> by_cases n : i=j <;> simp_all [swapBit]
lemma flipSwap_hom (i j d a b : ℕ) (hd : d<4) : flipSwap i j (combine d a b)=combine d (flipSwap i j a) (flipSwap i j b) := by
  apply Nat.eq_of_testBit_eq;intro k
  interval_cases d <;> simp [swapBit,combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor]

def turn (m i j a : ℕ) := flipSwap i j (flipSwap (m+i) (m+j) a)
lemma turnGood {m i j a : ℕ} (hi : i<m) (hj : j<m) (g : Good m a) : Good m (turn m i j a) := by
  intro k hk
  have hm : m≠0 := by omega
  have ki : k≠m+i := by omega
  have kj : k≠m+j := by omega
  have ii : i≠m+i := by omega
  have ij : i≠m+j := by omega
  have ji : j≠m+i := by omega
  have jj : j≠m+j := by omega
  have ui : m+k≠i := by omega
  have uj : m+k≠j := by omega
  by_cases x : k=i
  · subst k;simp [turn,swapBit,ii,ij,ji,jj,ui,uj,hm];exact g _ hj
  by_cases y : k=j
  · subst k;simp [turn,swapBit,x,ii,ij,ji,jj,ui,uj,hm];exact g _ hi
  · simpa [turn,swapBit,x,y,ki,kj,ui,uj] using g k hk

theorem relabelLive {m k S} (f : ℕ→ℕ) (fz : f 0=0) (inj : Function.Injective f)
    (op : ∀ d a b,d<4 → f (combine d a b)=combine d (f a) (f b))
    (labels : ∀ a,Good m a → Good m (f a)) (live : Live m k S) : Live m k (S.image f) := by
  induction live with
  | done hg hn =>
    simp only [Finset.image_singleton]
    exact Live.done (labels _ hg) (fun h => hn (inj (h.trans fz.symm)))
  | @step k U a b d hd ha hb ne fresh tail ih =>
    rw [Finset.image_insert,Finset.image_insert]
    rw [Finset.image_insert,op d a b hd] at ih
    apply Live.step hd (fun h => ha (inj (h.trans fz.symm))) (fun h => hb (inj (h.trans fz.symm))) (fun h => ne (inj h)) _ ih
    rw [←op d a b hd,←Finset.image_insert,←Finset.image_insert]
    exact fun h => fresh ((Finset.mem_image.mp h).elim (fun x hh => inj hh.2 ▸ hh.1))
def permute (m : ℕ) : List (ℕ×ℕ) → ℕ → ℕ
  | [],a => a
  | (i,j)::ss,a => permute m ss (turn m i j a)
theorem perm_live {m k S} (ss : List (ℕ×ℕ)) (safe : ∀ p∈ss,p.1<m ∧ p.2<m) (h : Live m k S) :
    Live m k (S.image (permute m ss)) := by
  induction ss generalizing S with
  | nil => simpa [permute] using h
  | cons p ss ih =>
    obtain ⟨i,j⟩ := p
    obtain ⟨hi,hj⟩ := safe _ (List.mem_cons_self)
    have fi (a b : ℕ) : Function.Injective (flipSwap a b) := fun x y e =>
      (flipSwap_twice a b x).symm.trans ((congrArg (flipSwap a b) e).trans (flipSwap_twice a b y))
    have inj : Function.Injective (turn m i j) := (fi i j).comp (fi (m+i) (m+j))
    have names := relabelLive (turn m i j) (by simp [turn,flipSwap]) inj
      (fun d a b hd => by simp [turn,flipSwap_hom _ _ _ _ _ hd]) (fun _ => turnGood hi hj) h
    simpa [permute,Finset.image_image,Function.comp_def] using ih (fun p hp => safe _ (List.mem_cons_of_mem _ hp)) names
theorem perm_feasible {m fuel : ℕ} {v w : List ℕ} (ss : List (ℕ×ℕ)) (safe : ∀ p∈ss,p.1<m ∧ p.2<m)
    (eq : (v.map (permute m ss)).toFinset=w.toFinset) (nw : w.Nodup) (h : feasible m fuel v) : feasible m fuel w := by
  obtain ⟨k,lim,ok,_⟩ := h
  refine ⟨k,lim,?_,nw⟩
  have tr := perm_live ss safe ok
  have imageEq : (v.map (permute m ss)).toFinset = v.toFinset.image (permute m ss) := by ext x;simp
  rw [←eq,imageEq]
  exact tr

def Excluded (m k : ℕ) (v : List ℕ) := ¬feasible m k v
def Block (m k : ℕ) (vs : List (List ℕ)) (i n : ℕ) := ∀ v∈(vs.drop i).take n,Excluded m k v
lemma blocks_cover {m k width q : ℕ} {vs : List (List ℕ)} (pw : 0<width) (size : vs.length≤q*width)
    (all : ∀ j : Fin q,Block m k vs (j.val*width) width) : ∀ v∈vs,Excluded m k v := by
  intro v hv
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hv
  have split := Nat.div_add_mod' i width
  have within := Nat.mod_lt i pw
  have bound : i/width<q := (Nat.div_lt_iff_lt_mul pw).2 (by omega)
  apply all ⟨i/width,bound⟩ _
  apply List.mem_iff_getElem.mpr
  have ix : i % width<((vs.drop (i/width*width)).take width).length := by simp only [List.length_take,List.length_drop];omega
  refine ⟨i % width,ix,?_⟩
  simp only [List.getElem_take,List.getElem_drop]
  simp [split]
lemma join_exclusions {m k : ℕ} {v : List ℕ} (term : terminal m v=false)
    (no : ∀ w∈successors m k v,Excluded m k w) : Excluded m (k+1) v := by
  intro h
  rcases move h with e|⟨w,hw,hf⟩
  · exact Bool.noConfusion (term.symm.trans e)
  · exact no w hw hf

structure FloorData where
  pairMask : ℕ
  lower : ℕ
  basis : List ℕ
deriving Inhabited
def Floor (m : ℕ) (s : FloorData) := ∀ k,Possible m k (0::s.basis) → s.lower≤k
theorem floorChecked {m : ℕ} {s : FloorData} (checked : start m (s.lower-1) (0::s.basis)=false) : Floor m s := by
  intro k poss
  by_contra small
  obtain ⟨j,S,le,live,sub⟩ := poss
  exact Bool.noConfusion (checked.symm.trans (start_complete live _ sub _ (by omega)))
lemma getMember {av : List ℕ} (zeroMem : 0∈av) (i : ℕ) : av.getD i 0∈av := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : av[i]? with
  | none => exact zeroMem
  | some t => exact List.mem_of_getElem? e

def instruction (av : List ℕ) (part : ℕ) :=
  let n := (part &&& 4095)-1
  combine (n % 4) (av.getD ((n >>> 2) &&& 15) 0) (av.getD ((n >>> 6) &&& 15) 0)
def replay : ℕ → ℕ → List ℕ → List ℕ
  | 0,_,av => av
  | k+1,code,av => if code=0 then av else replay k (code >>> 12) (av++[instruction av code])
def paidCount : ℕ → ℕ → ℕ
  | 0,_ => 0
  | k+1,code => if code=0 then 0 else paidCount k (code >>> 12)+1

theorem replay_back {m k : ℕ} (count code : ℕ) (av : List ℕ) (hasZero : 0∈av)
    (later : Possible m k (replay count code av)) : Possible m (k+paidCount count code) av := by
  induction count generalizing code av with
  | zero => simpa [replay,paidCount] using later
  | succ n ih =>
    by_cases stop : code=0
    · simpa [replay,paidCount,stop] using later
    rw [replay,ite_eq_right stop] at later
    have post := ih _ (av++[instruction av code]) (by simp [hasZero]) later
    let p := (code &&& 4095)-1
    have full := pullPaid (d:=p % 4) (Nat.mod_lt _ (by decide)) (getMember hasZero ((p >>> 2) &&& 15)) (getMember hasZero ((p >>> 6) &&& 15)) post
    obtain ⟨j,S,lim,live,sub⟩ := full
    refine ⟨j,S,?_,live,sub⟩
    rw [paidCount,ite_eq_right stop]
    have one (b : Bool) : b.toNat≤1 := by cases b <;> decide
    have bound := one (charge av (combine (p % 4) (av.getD ((p >>> 2) &&& 15) 0) (av.getD ((p >>> 6) &&& 15) 0)))
    omega

def contradictsFloor (m fuel : ℕ) (v : List ℕ) (s : FloorData) (code : ℕ) : Bool :=
  let r := min s.pairMask.log2 (m-1)
  let pv := v.map (slice m s.pairMask r)
  let av := replay 5 code (0::s.basis)
  fuel+paidCount 5 code<s.lower+pv.count 0 && pv.all (fun x => av.contains x)
lemma deadCount (f : ℕ→ℕ) {v : List ℕ} (nd : v.Nodup) :
    dead f v.toFinset=(v.map f).count 0 := by
  unfold dead
  have E : v.toFinset.filter (fun x => f x=0) = (v.filter (fun x => decide (f x=0))).toFinset := by ext x;simp
  rw [E,List.toFinset_card_of_nodup (nd.filter _)]
  simp only [List.count_eq_countP,List.countP_map]
  rw [List.countP_eq_length_filter]
  congr 2

theorem floor_consistent {m fuel : ℕ} (pos : 0<m) {v : List ℕ} (ok : feasible m fuel v) (s : FloorData)
    (known : Floor m s) (code : ℕ) : contradictsFloor m fuel v s code=false := by
  let r := min s.pairMask.log2 (m-1)
  let p := projection m s.pairMask r (show r<m by dsimp [r];omega)
  let pv := v.map p.toFun
  let av := replay 5 code (0::s.basis)
  obtain ⟨k,hk,live,nd⟩ := ok
  obtain ⟨l,T,lim,pr,inside⟩ := projectLive p live
  rw [deadCount _ nd] at lim
  apply Bool.eq_false_iff.mpr
  intro bad
  change (decide (fuel+paidCount 5 code < s.lower+pv.count 0) && pv.all (fun x => av.contains x))=true at bad
  simp only [Bool.and_eq_true] at bad
  obtain ⟨lo,mem⟩ := bad
  have low := of_decide_eq_true lo
  have final : Possible m l av := by
    refine ⟨l,T,le_rfl,pr,?_⟩
    intro x hx
    have active : x∈pv := by simpa [pv] using inside x hx
    exact List.contains_iff_mem.mp (List.all_eq_true.mp mem x active)
  have size := known _ (replay_back 5 code (0::s.basis) (by simp) final)
  change l+pv.count 0≤k at lim
  omega

def Memo := ℕ → FloorData × ℕ
def Certified (m : ℕ) (db : Memo) := ∀ i,Floor m (db i).1
inductive Advice where
  | plain
  | restrict (which : ℕ)
  | saved (index : ℕ)
  | fork (codes : ℕ) (nested : List Advice)
deriving Inhabited
def chooseAdvice (tag : ℕ) (gs : List Advice) : Advice :=
  if tag=1 then gs.headD .plain else if tag=0 then .plain else if tag<1024 then .restrict (tag-2) else .saved (tag-1024)
def memoRows (go : Advice → List ℕ → Bool) : List (List ℕ) → ℕ → List Advice → Bool
  | [],_,_ => false
  | v::vs,code,gs =>
    let tag := code &&& 4095
    go (chooseAdvice tag gs) v || memoRows go vs (code >>> 12) (if tag=1 then gs.tail else gs)
lemma memoRows_ok {go : Advice→List ℕ→Bool} {v : List ℕ} {vs : List (List ℕ)} (mem : v∈vs)
    (all : ∀ g,go g v=true) (code : ℕ) (gs : List Advice) : memoRows go vs code gs=true := by
  induction vs generalizing code gs with
  | nil => simp at mem
  | cons x xs ih =>
    rw [memoRows,Bool.or_eq_true]
    rcases List.mem_cons.mp mem with rfl|next
    · exact Or.inl (all _)
    · exact Or.inr (ih next _ _)
def audited (m : ℕ) (db : Memo) : ℕ → Advice → List ℕ → Bool
  | 0,_,v => terminal m v
  | k+1,.plain,v => search m (k+1) v
  | k+1,.restrict which,v => cutSearch m (zeroPairs m v which (full m)) (k+1) v
  | k+1,.saved i,v => !(contradictsFloor m (k+1) v (db i).1 (db i).2)
  | k+1,.fork code gs,v => terminal m v || memoRows (audited m db k) (successors m k v) code gs
theorem audited_complete {m : ℕ} (hm : 0<m) (db : Memo) (safe : Certified m db)
    (fuel : ℕ) (v : List ℕ) (h : feasible m fuel v) (g : Advice) : audited m db fuel g v=true := by
  induction fuel generalizing v g with
  | zero =>
    obtain ⟨j,lim,live,nd⟩ := h
    exact complete m 0 live lim v rfl nd
  | succ k ih =>
    cases g with
    | plain =>
      obtain ⟨j,lim,live,nd⟩ := h
      exact complete m (k+1) live lim v rfl nd
    | restrict which =>
      obtain ⟨j,lim,live,nd⟩ := h
      exact cut_complete hm live v rfl nd _ _ lim
    | saved i => simp [audited,floor_consistent hm h _ (safe i) _]
    | fork code gs =>
      rw [audited,Bool.or_eq_true]
      rcases move h with endNow|⟨w,hw,next⟩
      · exact Or.inl endNow
      · exact Or.inr (memoRows_ok hw (fun g => ih w next g) _ _)
lemma offAudit {m k v g} {db : Memo} (safe : Certified m db) (pos : 0<m) (e : audited m db k g v=false) : Excluded m k v := by
  intro h;exact Bool.noConfusion (e.symm.trans (audited_complete pos db safe k v h g))
lemma offMemoRows {m k : ℕ} {vs : List (List ℕ)} {i n code : ℕ} {gs : List Advice} {db : Memo}
    (safe : Certified m db) (pos : 0<m)
    (e : memoRows (audited m db k) ((vs.drop i).take n) code gs=false) : Block m k vs i n := by
  intro w hw h
  exact Bool.noConfusion (e.symm.trans (memoRows_ok hw (fun g => audited_complete pos db safe k w h g) code gs))

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def graph (x : Fin 7 → Bool) := ([(0,1),(1,2),(0,4),(1,5),(2,6),(3,5),(4,6),(6,3)] : List (Fin 7 × Fin 7)).any (fun e => x e.1 && x e.2)
def posBits : ℕ := 0x1c74e5c7c3464c58a94a8d0e8c98b0e84889d1e366bc1c326395aad4f9162662a51a84571e1e3b69d1e3761c19a858ad264589d0233569d1f3160e94a870b92a4c8b90a22950f103220c0c883
def negBits : ℕ := 0x1870e1c383060c10a142850a0c1830604080d1a3468c183060952a54a9122442850a04070e1c3868d1a3460c182850a122448910203468d1a3060c142850a122448910202850a102020408081
def sample (bank : ℕ) (i : Fin 87) (j : Fin 7) := bank.testBit (7*i.val+j.val)
def inputs : List ℕ := [0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def seeds : List Wire := inputs.map (fun a => (false,a))
theorem listed : ∀ i : Fin 87, seeds.map (read i.val)=List.ofFn (sample posBits i) ∧
    seeds.map (read (87+i.val))=List.ofFn (sample negBits i) := by decide +kernel
theorem labels : ∀ i : Fin 87, graph (sample posBits i)=true ∧ graph (sample negBits i)=false := by decide +kernel
theorem essential : ∀ a∈inputs, ∃ i : Fin 87, ∀ b∈inputs, b.testBit i.val≠b.testBit (87+i.val) → b=a := by decide +kernel
theorem initial {k S} (live : Live 87 k S) (sub : ∀ a∈S,a∈inputs) : S=inputs.toFinset := by
  apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
  intro a ha
  obtain ⟨i,h⟩ := essential a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
  exact h b (sub b hb) sep ▸ hb

def s00 : List ℕ := [0x3c000003c70000000000007800008f8e000002004000,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40]
def s01 : List ℕ := [0x3fc1e3ffffc00003c079c1ffc7c7ffffaab2afa5f797,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40]
def s02 : List ℕ := [0x1e00000000003c079c18007c0000008922d81b387,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40]
def s03 : List ℕ := [0x3c003fc38c0000000000007c0077071a22080240410,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40]
def s04 : List ℕ := [0x3c01e000000000000000007807c00400000004008200,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3ffffc00000000000000007ffffc4440444914488a40,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s05 : List ℕ := [0x3ffffc03c7000003c079c1fffffccfce4cdb3fc9fbc7,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3ffffc00000000000000007ffffc4440444914488a40,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s06 : List ℕ := [0x3c7000003c079c18000008b8e08922b817187,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3ffffc00000000000000007ffffc4440444914488a40,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s07 : List ℕ := [0x3fe1c000000000000000007f83c4040444910480840,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3ffffc00000000000000007ffffc4440444914488a40,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s08 : List ℕ := [0x804400082008020811085,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s09 : List ℕ := [0x3c3fe003c703c0f3c7f9cff8ffc19f9e9f97ef9ff3bf,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s10 : List ℕ := [0x3e00000003c0f007800e00f80110109705c01e0038,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s11 : List ℕ := [0x3c01e003c7000003c079c1f003808f0c08120f00e302,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s12 : List ℕ := [0x8c0011092820080040010,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40]
def s13 : List ℕ := [0x3ffe03ffffc3c0f007800e7ffc47ffffb7a5e2bf54bd,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40]
def s14 : List ℕ := [0x3e00000003c0f007800e003c4000001585609b10ad,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40]
def s15 : List ℕ := [0x3fc003ffffc00000000000770006ef6d202002204400,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40]
def s16 : List ℕ := [0x3e00000000000000000008fc400000040100080000,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s17 : List ℕ := [0x3ffffc000003c0f007800e7ffffd54d2d7cdf4df9afd,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s18 : List ℕ := [0x3c0f007800e00000110929384e09710bd,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s19 : List ℕ := [0x3fc1fc00000000000000007703bc4440404814408a40,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s20 : List ℕ := [0x3c0000003c001c01000808780080207800380,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s21 : List ℕ := [0x3c01e3c3ff3c0703f879f1f90fcf8ffe799e6ff3f3ef,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s22 : List ℕ := [0x3c0383c070038003001080f0070710c40720068,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s23 : List ℕ := [0x3c01e00007000000007801e80740080e00902801f007,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s24 : List ℕ := [0x80100901104409200a8,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s25 : List ℕ := [0x3e03c3f83fc7f3ff81fe19fccf97f2ff8fe7ff13fd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s26 : List ℕ := [0x3c3f83c0703f801f011008e8760680a07600340,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s27 : List ℕ := [0x3e00000003c0f007800e08f44010028681a00d1015,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s28 : List ℕ := [0x3c0003c07000000000000078200790e41000100,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s29 : List ℕ := [0x3fff83ffffff801f0552aaffff87ffffff223ea,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s30 : List ℕ := [0x3f8000003f801f011088805f0000006f202e8,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s31 : List ℕ := [0x3c0003f8fc000000442220780806f1b8002002,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s32 : List ℕ := [0x3c3f800000000000011000787f0200002200000,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40]
def s33 : List ℕ := [0x3fc003fffffc0703f801f07fc88ffffffb2ec7f647f8,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40]
def s34 : List ℕ := [0x3c0703f801f00008880000590e45d203e8,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40]
def s35 : List ℕ := [0x3fc0003c07c000000000006ec000780f822080044410,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40]
def s36 : List ℕ := [0x11088c0440400804400240,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s37 : List ℕ := [0x3fffffc3f83c0703f801f07fffffc7f07d4f57fa8be8,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s38 : List ℕ := [0x3c3f83c0703f801f000000383b0390643b201a8,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s39 : List ℕ := [0x3ffffc00000000000000006ef7704000044110088800,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s40 : List ℕ := [0x3c07800200100010408900781f000,0x3ff803fffe0022111221257ff007fffc00,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s41 : List ℕ := [0x3c01e003c73ff803ffffc1fa17d2afaf7ff22fffff87,0x3ff803fffe0022111221257ff007fffc00,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s42 : List ℕ := [0x3ff8003f860002101220217760007e0c00,0x3ff803fffe0022111221257ff007fffc00,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s43 : List ℕ := [0x3c01e003c70000000001c1d806c08e8a000228000387,0x3ff803fffe0022111221257ff007fffc00,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s44 : List ℕ := [0x3c00007800000100000001780009f1000,0x3ff803fffe0022111221257ff007fffc00,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s45 : List ℕ := [0x3e0000003ff8f3fffe0e2afd5331b7fff5e7fffcbd,0x3ff803fffe0022111221257ff007fffc00,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s46 : List ℕ := [0x3c3803f87e00220112212568700760ec00,0x3ff803fffe0022111221257ff007fffc00,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s47 : List ℕ := [0x3e0000000000f000000e08ec4110928005e00000bd,0x3ff803fffe0022111221257ff007fffc00,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s48 : List ℕ := [0x3c0003f800000000020120790007f20000,0x3ff803fffe0022111221257ff007fffc00,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s49 : List ℕ := [0x3c3f83fff03fffff033199fa7f57ffe47ffffe8,0x3ff803fffe0022111221257ff007fffc00,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s50 : List ℕ := [0x3f80007fe00221110200506f0000dfc00,0x3ff803fffe0022111221257ff007fffc00,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s51 : List ℕ := [0x3c3f80007000001f011088d86d0000e400003e8,0x3ff803fffe0022111221257ff007fffc00,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s52 : List ℕ := [0x3ff80000000000000220007ff001002000,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s53 : List ℕ := [0x3fc003ffffffffe00663337fb2d7ffffffffd02,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s54 : List ℕ := [0x3fffe002211100125000006ffdc00,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s55 : List ℕ := [0x3fc000007fc000000442225da08000ff8000102,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s56 : List ℕ := [0x2200022125222002244400,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40]
def s57 : List ℕ := [0x3fc003fffffff803fffe007fd117fffffff087fffc10,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40]
def s58 : List ℕ := [0x3ff803fffe0000111000005dd005dbb800,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40]
def s59 : List ℕ := [0x3fc003ffffc000000000005dc005deda800080000010,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40]
def s60 : List ℕ := [0x2211100000444004488800,0x3ff803fffe0022111221257ff007fffc00,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s61 : List ℕ := [0x3ffffc00003ff803fffe007ffffe65657ff917fffe40,0x3ff803fffe0022111221257ff007fffc00,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s62 : List ℕ := [0x3ff803fffe0000000221253bb003b77400,0x3ff803fffe0022111221257ff007fffc00,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s63 : List ℕ := [0x3ffffc00000000000000005deeec4440000910000240,0x3ff803fffe0022111221257ff007fffc00,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s64 : List ℕ := [0x4002008a08089229002102,0x3fc003ffffc000000442227fa087ffff9002102,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s65 : List ℕ := [0x3c01e3ffc73fffffc079c1fc27e7ff8e7fffff81f387,0x3fc003ffffc000000442227fa087ffff9002102,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s66 : List ℕ := [0x3fc003ffffc0000000420277000776dd0000000,0x3fc003ffffc000000442227fa087ffff9002102,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s67 : List ℕ := [0x3c01e003c7000003c079c1b805c0058600000681d285,0x3fc003ffffc000000442227fa087ffff9002102,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s68 : List ℕ := [0x3c0f000000000200110001785e0000000,0x3fc003ffffc000000442227fa087ffff9002102,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s69 : List ℕ := [0x3e03fc003ffffc07800e4cfe67fa9afffff99f31bf,0x3fc003ffffc000000442227fa087ffff9002102,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s70 : List ℕ := [0x3fc003c3f0c000000440226ea08687a19002102,0x3fc003ffffc000000442227fa087ffff9002102,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s71 : List ℕ := [0x3e00000000000007800e08dc4000928000009f10bd,0x3fc003ffffc000000442227fa087ffff9002102,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s72 : List ℕ := [0x3fc00000000000000440007fa08222080000000,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3ffffc00000000000000007ffffc4440444914488a40]
def s73 : List ℕ := [0x3fc003fffffffffc0000007fe227fffffffffb246512,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3ffffc00000000000000007ffffc4440444914488a40]
def s74 : List ℕ := [0x3ffffc00000000222000005ddf79002102,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3ffffc00000000000000007ffffc4440444914488a40]
def s75 : List ℕ := [0x3fc00003ffc000000000003bc00005f7800002244410,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3ffffc00000000000000007ffffc4440444914488a40]
def s76 : List ℕ := [0x4422244000444910000000,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s77 : List ℕ := [0x3ffffffc003ffffc0000007ffffffe487ffffd48ab42,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s78 : List ℕ := [0x3fc003ffffc000000000003ba083bb6e9002102,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s79 : List ℕ := [0x3ffffc00000000000000003bddd80440000004488a40,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s80 : List ℕ := [0x3fc00000000000000000007fc0044440000000000000,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102]
def s81 : List ℕ := [0x3fffffffffc000000000007fffffffffe669966cce50,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102]
def s82 : List ℕ := [0x3ffffc00000000000000003bbbfa22082244410,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102]
def s83 : List ℕ := [0x3ffc0000000000000000003ff80000444914488a40,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102]
def firstLayer : List (List ℕ) := [s00,s01,s02,s03,s04,s05,s06,s07,s08,s09,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33,s34,s35,s36,s37,s38,s39,s40,s41,s42,s43,s44,s45,s46,s47,s48,s49,s50,s51,s52,s53,s54,s55,s56,s57,s58,s59,s60,s61,s62,s63,s64,s65,s66,s67,s68,s69,s70,s71,s72,s73,s74,s75,s76,s77,s78,s79,s80,s81,s82,s83]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem firstLayer_eq : successors 87 9 inputs=firstLayer := by decide +kernel
def perm0 : List (ℕ×ℕ) := []
def perm1 : List (ℕ×ℕ) := [(0,11),(1,10),(2,68),(3,67),(4,69),(5,6),(7,22),(8,21),(9,20),(12,15),(13,14),(16,72),(17,71),(18,73),(19,70),(23,26),(24,25),(27,48),(28,47),(29,81),(30,80),(31,82),(32,79),(33,53),(34,54),(35,52),(36,50),(37,51),(38,49),(39,85),(40,84),(41,86),(42,83),(43,56),(44,58),(45,57),(46,55),(59,61),(60,62),(63,65),(64,66),(74,76),(77,78)]
def perm2 : List (ℕ×ℕ) := [(0,28),(1,27),(2,69),(3,67),(4,68),(5,6),(7,35),(8,33),(9,34),(10,48),(11,47),(12,62),(13,59),(14,61),(15,60),(16,82),(17,80),(18,81),(19,79),(20,54),(21,53),(22,52),(23,66),(24,63),(25,65),(26,64),(29,73),(30,71),(31,72),(32,70),(36,51),(37,50),(38,49),(39,86),(40,84),(41,85),(42,83),(43,57),(44,58),(45,56),(46,55),(74,77),(76,78)]
def perm3 : List (ℕ×ℕ) := [(0,47),(1,48),(2,4),(7,52),(8,53),(9,54),(10,27),(11,28),(12,60),(13,61),(14,59),(15,62),(16,31),(17,30),(18,29),(19,32),(20,34),(21,33),(22,35),(23,64),(24,65),(25,63),(26,66),(36,37),(39,41),(43,45),(50,51),(56,57),(68,69),(70,79),(71,80),(72,82),(73,81),(74,78),(76,77),(85,86)]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem safe0 : ∀ p∈perm0,p.1<87 ∧ p.2<87 := by
  have good : perm0.all (fun p => decide (p.1<87 ∧ p.2<87))=true := by decide +kernel
  intro p hp;exact of_decide_eq_true (List.all_eq_true.mp good p hp)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem safe1 : ∀ p∈perm1,p.1<87 ∧ p.2<87 := by
  have good : perm1.all (fun p => decide (p.1<87 ∧ p.2<87))=true := by decide +kernel
  intro p hp;exact of_decide_eq_true (List.all_eq_true.mp good p hp)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem safe2 : ∀ p∈perm2,p.1<87 ∧ p.2<87 := by
  have good : perm2.all (fun p => decide (p.1<87 ∧ p.2<87))=true := by decide +kernel
  intro p hp;exact of_decide_eq_true (List.all_eq_true.mp good p hp)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem safe3 : ∀ p∈perm3,p.1<87 ∧ p.2<87 := by
  have good : perm3.all (fun p => decide (p.1<87 ∧ p.2<87))=true := by decide +kernel
  intro p hp;exact of_decide_eq_true (List.all_eq_true.mp good p hp)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym3 : feasible 87 9 s03 → feasible 87 9 s02 := perm_feasible perm3 safe3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym12 : feasible 87 9 s12 → feasible 87 9 s08 := perm_feasible perm3 safe3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym13 : feasible 87 9 s13 → feasible 87 9 s09 := perm_feasible perm3 safe3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym14 : feasible 87 9 s14 → feasible 87 9 s10 := perm_feasible perm3 safe3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym15 : feasible 87 9 s15 → feasible 87 9 s11 := perm_feasible perm3 safe3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym19 : feasible 87 9 s19 → feasible 87 9 s18 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym28 : feasible 87 9 s28 → feasible 87 9 s20 := perm_feasible perm2 safe2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym29 : feasible 87 9 s29 → feasible 87 9 s21 := perm_feasible perm2 safe2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym30 : feasible 87 9 s30 → feasible 87 9 s22 := perm_feasible perm2 safe2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym31 : feasible 87 9 s31 → feasible 87 9 s23 := perm_feasible perm2 safe2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym32 : feasible 87 9 s32 → feasible 87 9 s20 := perm_feasible perm3 safe3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym33 : feasible 87 9 s33 → feasible 87 9 s21 := perm_feasible perm3 safe3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym34 : feasible 87 9 s34 → feasible 87 9 s22 := perm_feasible perm3 safe3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym35 : feasible 87 9 s35 → feasible 87 9 s23 := perm_feasible perm3 safe3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym36 : feasible 87 9 s36 → feasible 87 9 s24 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym37 : feasible 87 9 s37 → feasible 87 9 s25 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym38 : feasible 87 9 s38 → feasible 87 9 s26 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym39 : feasible 87 9 s39 → feasible 87 9 s27 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym43 : feasible 87 9 s43 → feasible 87 9 s42 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym44 : feasible 87 9 s44 → feasible 87 9 s04 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym45 : feasible 87 9 s45 → feasible 87 9 s05 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym46 : feasible 87 9 s46 → feasible 87 9 s06 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym47 : feasible 87 9 s47 → feasible 87 9 s07 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym48 : feasible 87 9 s48 → feasible 87 9 s20 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym49 : feasible 87 9 s49 → feasible 87 9 s21 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym50 : feasible 87 9 s50 → feasible 87 9 s23 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym51 : feasible 87 9 s51 → feasible 87 9 s22 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym52 : feasible 87 9 s52 → feasible 87 9 s00 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym53 : feasible 87 9 s53 → feasible 87 9 s01 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym54 : feasible 87 9 s54 → feasible 87 9 s02 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym55 : feasible 87 9 s55 → feasible 87 9 s02 := perm_feasible perm2 safe2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym59 : feasible 87 9 s59 → feasible 87 9 s58 := perm_feasible perm2 safe2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym60 : feasible 87 9 s60 → feasible 87 9 s08 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym61 : feasible 87 9 s61 → feasible 87 9 s09 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym62 : feasible 87 9 s62 → feasible 87 9 s11 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym63 : feasible 87 9 s63 → feasible 87 9 s10 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym64 : feasible 87 9 s64 → feasible 87 9 s56 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym65 : feasible 87 9 s65 → feasible 87 9 s57 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym66 : feasible 87 9 s66 → feasible 87 9 s58 := perm_feasible perm3 safe3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym67 : feasible 87 9 s67 → feasible 87 9 s58 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym68 : feasible 87 9 s68 → feasible 87 9 s04 := perm_feasible perm2 safe2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym69 : feasible 87 9 s69 → feasible 87 9 s05 := perm_feasible perm2 safe2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym70 : feasible 87 9 s70 → feasible 87 9 s06 := perm_feasible perm2 safe2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym71 : feasible 87 9 s71 → feasible 87 9 s07 := perm_feasible perm2 safe2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym72 : feasible 87 9 s72 → feasible 87 9 s40 := perm_feasible perm2 safe2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym73 : feasible 87 9 s73 → feasible 87 9 s41 := perm_feasible perm2 safe2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym74 : feasible 87 9 s74 → feasible 87 9 s42 := perm_feasible perm3 safe3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym75 : feasible 87 9 s75 → feasible 87 9 s42 := perm_feasible perm2 safe2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym76 : feasible 87 9 s76 → feasible 87 9 s08 := perm_feasible perm2 safe2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym77 : feasible 87 9 s77 → feasible 87 9 s09 := perm_feasible perm2 safe2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym78 : feasible 87 9 s78 → feasible 87 9 s11 := perm_feasible perm2 safe2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym79 : feasible 87 9 s79 → feasible 87 9 s10 := perm_feasible perm2 safe2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym80 : feasible 87 9 s80 → feasible 87 9 s04 := perm_feasible perm3 safe3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym81 : feasible 87 9 s81 → feasible 87 9 s05 := perm_feasible perm3 safe3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym82 : feasible 87 9 s82 → feasible 87 9 s06 := perm_feasible perm3 safe3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym83 : feasible 87 9 s83 → feasible 87 9 s07 := perm_feasible perm3 safe3 (by decide +kernel) (by decide +kernel)

def floorData0 : FloorData := ⟨0x7f83f7071f76dd07e0c78,8,[0x0,0x3c0000000380e007000c00f80110109705c01e0038,0x3803838060038003001080f0070710c40720068,0x3bb0003f060002101220217760007e0c00,0x3b8003bb6e80000007c27e7ff8e7fffff81f387,0x3fc3e3ffffc44917c0f9c3ffc7c7ffffaab2afa5f797,0x3ffffc47c7044917c0f9c3fffffccfce4cdb3fc9fbc7]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof0 : Floor 87 floorData0 := floorChecked (by decide +kernel)
def floorData1 : FloorData := ⟨0x6ef770780f86f1b80dfc17,8,[0x3c85e7c3ff3c8723f979f5f90fcf8ffe799e6ff3f3ef,0x3a0000000340d006800a08f44010028681a00d1015,0x0,0x3780006fe00221110200506f0000dfc00,0x3c000378dc000000552aaffff87ffffff223ea,0x3fc447fffffc8723f901f47fc88ffffffb2ec7f647f8,0x3fffffc3f83c8723f901f47fffffc7f07d4f57fa8be8]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof1 : Floor 87 floorData1 := floorChecked (by decide +kernel)
def floorData2 : FloorData := ⟨0x5deeeddeda800ff80003ff,8,[0x3d09e913d7bff803ffffc1fa17d2afaf7ff22fffff87,0x360000000000f000000e08ec4110928005e00000bd,0x2c3680007000001f011088d86d0000e400003e8,0x0,0x2ec000007fc000000663337fb2d7ffffffffd02,0x3fc88bfffffff803fffe007fd117fffffff087fffc10,0x3ffffd1092bff803fffe007ffffe65657ff917fffe40]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof2 : Floor 87 floorData2 := floorChecked (by decide +kernel)
def floorData3 : FloorData := ⟨0x3bddd805f7800006ffdefd,8,[0x3e11f3ffc73fffffc079c1fc27e7ff8e7fffff81f387,0x2e00000000000007800e08dc4000928000009f10bd,0x2f800000378017011088805f0000006f202e8,0x37fee00663337fb2d7ffffffffd02,0x0,0x3fd113fffffffffc8010817fe227fffffffffb246512,0x3ffffffd043ffffc8010817ffffffe487ffffd48ab42]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof3 : Floor 87 floorData3 := floorChecked (by decide +kernel)
def floorData4 : FloorData := ⟨0x3ff800005ddf7ddbbbef,8,[0x1e00000000002c059c18007c0000008922d81b387,0x3ffe03ffffd3d0f117a20e7ffc47ffffb7a5e2bf54bd,0x2c0702e801f00008880000590e45d203e8,0x2ee802eddc0000111000005dd005dbb800,0x2eefbc0000007fe227fffffffffb246512,0x0,0x3fffffffffd110411222087fffffffffe669966cce50]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof4 : Floor 87 floorData4 := floorChecked (by decide +kernel)
def floorData5 : FloorData := ⟨0x7703beef6d687a1f60ef42,7,[0x3c7fe08bcf4bc2f3cff9dff8ffc19f9e9f97ef9ff3bf,0x0,0x343b0340503b001a011008e8760680a07600340,0x343803b07600220112212568700760ec00,0x37400343d0c0000004cfe67fa9afffff99f31bf,0x3ffe23ffffcbc2f04f885efffc47ffffb7a5e2bf54bd,0x3ffffc88494bc2f04f885efffffd54d2d7cdf4df9afd]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof5 : Floor 87 floorData5 := floorChecked (by decide +kernel)
def floorData6 : FloorData := ⟨0x3d81800718000007e0c78,7,[0x0,0x2c00000000000007000c00d80000108000001e0038,0x380000003800300108080070000000720068,0x3f06007e37f7ffaf7fffffffff87,0x0,0x3fd3f3ffffffffffc0f9c3ffe7e7ffffffffffa5f797,0x3fffffffc73fffffc0f9c3ffffffffce7fffffc9fbc7]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof6 : Floor 87 floorData6 := floorChecked (by decide +kernel)
def floorData7 : FloorData := ⟨0x2ee80000000f780003ef,7,[0x16000000000000001c18006c00000000228000387,0x3ffe8bfffffff8f3fffe0e7ffd57fffffff5e7fffcbd,0x7000001f00008880000000e400003e8,0x0,0x7bc0000007ff337fffffffffffffd12,0x0,0x3ffffffffffff843fffe087ffffffffffff997fffe50]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof7 : Floor 87 floorData7 := floorChecked (by decide +kernel)
def floorData8 : FloorData := ⟨0x3bbbfbbb6ebb775bf,7,[0x1c7000001c038c18000008b8e08922b817187,0x1c07003800e00000110929384e09710bd,0x3fffffe3f83e278bfc45f07fffffc7f07d4f57fa8be8,0x1dd801dbba007ffffe65657ff917fffe40,0x3ffffffe203ffffe2445207ffffffe487ffffd48ab42,0x3fffffffffe2248a2445207fffffffffe669966cce50,0x0]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof8 : Floor 87 floorData8 := floorChecked (by decide +kernel)
def floorData9 : FloorData := ⟨0x7003e6061606810600c40,5,[0x0,0x0,0x3003030040030002001000e0060600800600040,0x3030003006000200122021606000600c00,0x330003034080000007cffe7ff9effffff9ff3bf,0x3fffe3ffffcfcbf7cff9dfffffc7ffffbfb7efbff7bf,0x3ffffccfcf4fcbf7cff9dffffffddfdedfdfffdffbff]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof9 : Floor 87 floorData9 := floorChecked (by decide +kernel)
def floorData10 : FloorData := ⟨0x6f03070018661900c0c10,5,[0x0,0x380000000300c006000800f00010008601800c0010,0x0,0x3300006060002101020010660000c0c00,0x38000330c80000007d2feffffe7ffffff3f3ef,0x3fc7e7fffffccf37f9f9f7ffcfcffffffbbeeff7f7ff,0x3fffffc7ff3ccf37f9f9f7ffffffcffe7ddf7ffbfbef]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof10 : Floor 87 floorData10 := floorChecked (by decide +kernel)
def floorData11 : FloorData := ⟨0x660330680d00701800ec02,5,[0x3cffe7cbff7fc7f3fff9fff9ffcf9ffeff9feffff3ff,0x0,0x0,0x3800007600220110200500700000ec00,0x340000380c0000005dfeeffffaffffffff33ff,0x3ffe67ffffffc7f3ff89fefffccfffffffafe7ff57fd,0x3fffffcbf97fc7f3ff89feffffffd7f2ffcff7ff9bfd]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof11 : Floor 87 floorData11 := floorChecked (by decide +kernel)
def floorData12 : FloorData := ⟨0x5e82d5050800dd0000078,5,[0x0,0x340000000000e000000c00e80110108005c0000038,0x2802800060000003001080d0050000c40000068,0x0,0x2a8000006e80000007e37f7ffaf7fffffffff87,0x3fcbebfffffff917ffffc3ffd7d7fffffff2afffff97,0x3ffffd57d7bff917ffffc3fffffeefef7ffb3fffffc7]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof12 : Floor 87 floorData12 := floorChecked (by decide +kernel)
def floorData13 : FloorData := ⟨0x4ce660580a8001b8000017,5,[0x3d8defd3ffbfff23fffff5fb1fdfafff7ffe6fffffef,0x320000000000d000000a08e44010028001a0000015,0x0,0x0,0x2c000000dc000000773bbffffd7fffffffffea,0x3fcccfffffffff23fffff47fd99ffffffffec7fffff8,0x3fffffd3fabfff23fffff47fffffe7f57fff57ffffe8]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof13 : Floor 87 floorData13 := floorChecked (by decide +kernel)
def floorData14 : FloorData := ⟨0x2ad55000078000000ddc15,5,[0x3e95f7ffff3ffffff979f5fd2feffffe7ffffff3f3ef,0x2a00000000000006800a08d44000028000000d1015,0x0,0x6ee00773bbffffd7fffffffffea,0x0,0x3fd557fffffffffff911f57feaaffffffffffff667fa,0x3ffffffffc3ffffff911f57ffffffff87ffffffaabea]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof14 : Floor 87 floorData14 := floorChecked (by decide +kernel)
def floorData15 : FloorData := ⟨0x19ccc804d28000000002fd,5,[0x3f19fbffd7bfffffffffc1fe37f7ffaf7fffffffff87,0x2600000000000000000e08cc4000928000000000bd,0x268000000000170773bbffffd7fffffffffea,0x0,0x0,0x3fd99bfffffffffffffe817ff337fffffffffffffd12,0x3ffffffd96bffffffffe817fffffff6d7fffffffff42]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof15 : Floor 87 floorData15 := floorChecked (by decide +kernel)
def floorData16 : FloorData := ⟨0x38380000554d505a0868,5,[0x0,0x3fffe3ffffd7d9f7d7fbcfffffc7ffffbfb7efbff7bf,0x2806002800300008080000510c40520068,0x2aa0002d040000101000005540005a0800,0x2aa6a80000007fe7e7ffffffffffa5f797,0x0,0x3fffffffffd55957d2fbcbffffffffffeefbbfedffd7]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof16 : Floor 87 floorData16 := floorChecked (by decide +kernel)
def floorData17 : FloorData := ⟨0x3b80000485a1d40ab42,5,[0x3fffe3ffffdbd2f3dffbdfffffc7ffffbfb7efbff7bf,0x0,0x240502a001a00000880000480a05400340,0x242802a05400000110000048500540a800,0x242d0c0000007ffe67fffffffffbbf75bf,0x0,0x3fffffffffdbd2f15faa5efffffffffff7edf6ffdefd]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof17 : Floor 87 floorData17 := floorChecked (by decide +kernel)
def floorData18 : FloorData := ⟨0x3770000004d13809b807,5,[0x1a00000000000005801800740000000902801b007,0x3ffe47ffffffd7f3ffa3fe7ffccfffffffafe7ff57fd,0x0,0x2680004dc00001110000004d00009b800,0x2689c0000007feaaffffffffffff667fa,0x0,0x3ffffffffffd9763fb23fc7fffffffffff6fd7fecff8]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof18 : Floor 87 floorData18 := floorChecked (by decide +kernel)
def floorData19 : FloorData := ⟨0x1dd80000000004db9aed,5,[0xe000000000024049408005c00000000004819285,0x3fff13fffffffffd97b28f7ffe67fffffffffbbf75bf,0x26801700008880000000004d202e8,0x26dcc007ff337fffffffffffffd12,0x0,0x0,0x3ffffffffffffffd9232897fffffffffffffff6cef52]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof19 : Floor 87 floorData19 := floorChecked (by decide +kernel)
def floorData20 : FloorData := ⟨0x380f82b0a8057417,5,[0x7000000003801800000080e009028017007,0x1405002800a00000010028280a0051015,0x0,0x1580002ba007fffffe7f57fff57ffffe8,0x3ffffffff83ffffffd45f47ffffffff87ffffffaabea,0x3ffffffffffea7abfd45f47fffffffffff6fd7fecff8,0x0]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof20 : Floor 87 floorData20 := floorChecked (by decide +kernel)
def floorData21 : FloorData := ⟨0x19a9a8006e80001bf,5,[0x1450000000000c18000008a8a000228000187,0x7000000e7fffff75f7fffdf7fffefd,0x3ffffff3fabfff8bfffff07fffffe7f57fff57ffffe8,0x0,0x3ffffffeb2bfffffffff207fffffff6d7fffffffff42,0x3ffffffffffffc8bffff207ffffffffffff997fffe50,0x0]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof21 : Floor 87 floorData21 := floorChecked (by decide +kernel)
def floorData22 : FloorData := ⟨0x1b7800002b754bd,5,[0x3fffffffe73fffffe47de1ffffffffce7fffffc9fbc7,0x3800e00000000928000009710bd,0x3ffffffffc3ffffffc55f17ffffffff87ffffffaabea,0x15baa007fffffff6d7fffffffff42,0x0,0x3ffffffffffffffea455a17fffffffffffffff6cef52,0x0]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof22 : Floor 87 floorData22 := floorChecked (by decide +kernel)
def floorData23 : FloorData := ⟨0x600306001006010000c00,4,[0x0,0x0,0x0,0x30000006000200102001006000000c00,0x30000030080000007dffeffffefffffffff3ff,0x3fffe7ffffffcff7fff9ffffffcfffffffbfeffff7ff,0x3fffffcfff7fcff7fff9ffffffffdffeffdffffffbff]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof23 : Floor 87 floorData23 := floorChecked (by decide +kernel)
def floorData24 : FloorData := ⟨0x5502acce48000a18000342,4,[0x3d7fe99bdffffaf3ffffdffaffd3bfbffff7efffffbf,0x0,0x243200005000001a011008c8640000a00000340,0x0,0x2640000050c0000006eff77fbbffffffffffdbf,0x3ffeabfffffffaf3fffe5efffd57fffffff5e7fffcbd,0x3ffffd98dbfffaf3fffe5effffff75f7fffdf7fffefd]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof24 : Floor 87 floorData24 := floorChecked (by decide +kernel)
def floorData25 : FloorData := ⟨0x330198056500000660ce40,4,[0x3e7ff3ffcf7fffffcff9dffcffe7ff9effffff9ff3bf,0x0,0x2b00000033001201100880560000006600240,0x33066006eff77fbbffffffffffdbf,0x0,0x3fff33fffffffffccf98dffffe67fffffffffbbf75bf,0x3ffffffd4d7ffffccf98dffffffffedafffffddfbbff]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof25 : Floor 87 floorData25 := floorChecked (by decide +kernel)
def floorData26 : FloorData := ⟨0x300180061000000600c40,4,[0x0,0x0,0x300000003000200100080060000000600040,0x3006007efff7ffbfffffffffffbf,0x0,0x3ffff3ffffffffffcff9dfffffe7ffffffffffbff7bf,0x3fffffffcf7fffffcff9dfffffffffdeffffffdffbff]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof26 : Floor 87 floorData26 := floorChecked (by decide +kernel)
def floorData27 : FloorData := ⟨0x2d01000018000000c0c10,4,[0x0,0x2800000000000006000800d00000008000000c0010,0x0,0x606007f3fffffff7fffffffffef,0x0,0x3fd7f7fffffffffff9f9f7ffefeffffffffffff7f7ff,0x3fffffffff3ffffff9f9f7fffffffffe7ffffffbfbef]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof27 : Floor 87 floorData27 := floorChecked (by decide +kernel)
def floorData28 : FloorData := ⟨0x1c8080050800000000078,4,[0x0,0x2400000000000000000c00c8000010800000000038,0x280000000000307f3fffffff7fffffffffef,0x0,0x0,0x3fdbfbffffffffffffffc3fff7f7ffffffffffffff97,0x3fffffffd7bfffffffffc3ffffffffef7fffffffffc7]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof28 : Floor 87 floorData28 := floorChecked (by decide +kernel)
def floorData29 : FloorData := ⟨0x330000000501800a802,4,[0x3fffe7ffffffd7f3fffbffffffcfffffffbfeffff7ff,0x0,0x0,0x2800005400000110000000500000a800,0x280c0000007ffeefffffffffffff77ff,0x0,0x3fffffffffffd7f3ffabfeffffffffffffeff7ffdffd]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof29 : Floor 87 floorData29 := floorChecked (by decide +kernel)
def floorData30 : FloorData := ⟨0x28280000000d50000068,4,[0x0,0x3fffebfffffff9f7ffffcfffffd7fffffff7efffffbf,0x6000000300008080000000c40000068,0x0,0x6a80000007ff7f7ffffffffffffff97,0x0,0x3ffffffffffff957ffffcbfffffffffffffbbfffffd7]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof30 : Floor 87 floorData30 := floorChecked (by decide +kernel)
def floorData31 : FloorData := ⟨0x2a80000000a18000342,4,[0x3fffebfffffffaf3ffffdfffffd7fffffff7efffffbf,0x0,0x5000001a00000880000000a00000340,0x0,0x50c0000007fff77fffffffffffffdbf,0x0,0x3ffffffffffffaf3fffe5efffffffffffffdf7fffefd]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof31 : Floor 87 floorData31 := floorChecked (by decide +kernel)
def floorData32 : FloorData := ⟨0x26600000000138000007,4,[0x12000000000000000018006400000000028000007,0x3ffecffffffffff3fffffe7ffddfffffffffe7fffffd,0x0,0x0,0x9c0000007ffbbffffffffffffffffa,0x0,0x3fffffffffffff63fffffc7fffffffffffffd7fffff8]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof32 : Floor 87 floorData32 := floorChecked (by decide +kernel)
def floorData33 : FloorData := ⟨0x181800000000005a0868,4,[0x0,0x3ffff3ffffffffffd7fbcfffffe7ffffffffffbff7bf,0x2800300008080000000000520068,0x2d04007ff7f7ffffffffffffff97,0x0,0x0,0x3fffffffffffffffd2fbcbffffffffffffffffedffd7]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof33 : Floor 87 floorData33 := floorChecked (by decide +kernel)
def floorData34 : FloorData := ⟨0xcc800000000000002ed,4,[0x6000000000000001408004c00000000000000285,0x3fff9bfffffffffffffe8f7fff77fffffffffffffdbf,0x1707ffbbffffffffffffffffa,0x0,0x0,0x0,0x3ffffffffffffffffffe897fffffffffffffffffff52]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof34 : Floor 87 floorData34 := floorChecked (by decide +kernel)
def floorData35 : FloorData := ⟨0x33031b324c0360438,4,[0x0,0x1806003000c00000110109304c0160038,0x3fffffe7ff3e6f9ffcfdf3ffffffcffe7ddf7ffbfbef,0x1990001b02007ffffeefef7ffb3fffffc7,0x3fffffffe73fffffe4fde3ffffffffce7fffffc9fbc7,0x3fffffffffe66d9fe4fde3ffffffffffeefbbfedffd7,0x0]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof35 : Floor 87 floorData35 := floorChecked (by decide +kernel)
def floorData36 : FloorData := ⟨0x180a8000a8000017,4,[0x5000000000001800000080a000028000007,0x5000000a7ffffff7f7fffff7fffffd,0x0,0x0,0x3ffffffffabffffffffff47ffffffffd7fffffffffea,0x3fffffffffffffabfffff47fffffffffffffd7fffff8,0x0]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof36 : Floor 87 floorData36 := floorChecked (by decide +kernel)
def floorData37 : FloorData := ⟨0x31800000360438,4,[0x0,0x3000c0000000010800000160038,0x3fffffffff3ffffffcfdf3fffffffffe7ffffffbfbef,0x1b02007fffffffef7fffffffffc7,0x0,0x3fffffffffffffffe4fde3ffffffffffffffffedffd7,0x0]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof37 : Floor 87 floorData37 := floorChecked (by decide +kernel)
def floorData38 : FloorData := ⟨0x7800000055415,4,[0x3fffffffff3ffffffd7df5fffffffffe7ffffffbfbef,0x2800a0000000002800000051015,0x0,0x2aa007ffffffffd7fffffffffea,0x0,0x3ffffffffffffffffd55f57ffffffffffffffffeeffa,0x0]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof38 : Floor 87 floorData38 := floorChecked (by decide +kernel)
def floorData39 : FloorData := ⟨0x1996699331af,4,[0xc018c18000000000089229813187,0xc0300180067ffffffffff7edf6ffdefd,0x3fffffffffff37cbfe67f87fffffffffff6fd7fecff8,0x3ffffffffffffccbffff287ffffffffffff997fffe50,0x3fffffffffffffff3667287fffffffffffffff6cef52,0x0,0x0]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof39 : Floor 87 floorData39 := floorChecked (by decide +kernel)
def floorData40 : FloorData := ⟨0x6680001af,4,[0xc18000000000000228000187,0x300000067ffffffffffffdf7fffefd,0x3fffffffffffffcbfffff87fffffffffffffd7fffff8,0x0,0x3fffffffffffffffffff287fffffffffffffffffff52,0x0,0x0]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof40 : Floor 87 floorData40 := floorChecked (by decide +kernel)
def floorLibrary : List FloorData := [floorData0,floorData1,floorData2,floorData3,floorData4,floorData5,floorData6,floorData7,floorData8,floorData9,floorData10,floorData11,floorData12,floorData13,floorData14,floorData15,floorData16,floorData17,floorData18,floorData19,floorData20,floorData21,floorData22,floorData23,floorData24,floorData25,floorData26,floorData27,floorData28,floorData29,floorData30,floorData31,floorData32,floorData33,floorData34,floorData35,floorData36,floorData37,floorData38,floorData39,floorData40]
def emptyFloor : FloorData := ⟨0,0,[]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem storedFloor (i : ℕ) : Floor 87 (floorLibrary.getD i emptyFloor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : floorLibrary[i]? with
  | none => exact fun _ _ => Nat.zero_le _
  | some s =>
    have mem := List.mem_of_getElem? e
    simp only [floorLibrary,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact floorProof0
    · exact floorProof1
    · exact floorProof2
    · exact floorProof3
    · exact floorProof4
    · exact floorProof5
    · exact floorProof6
    · exact floorProof7
    · exact floorProof8
    · exact floorProof9
    · exact floorProof10
    · exact floorProof11
    · exact floorProof12
    · exact floorProof13
    · exact floorProof14
    · exact floorProof15
    · exact floorProof16
    · exact floorProof17
    · exact floorProof18
    · exact floorProof19
    · exact floorProof20
    · exact floorProof21
    · exact floorProof22
    · exact floorProof23
    · exact floorProof24
    · exact floorProof25
    · exact floorProof26
    · exact floorProof27
    · exact floorProof28
    · exact floorProof29
    · exact floorProof30
    · exact floorProof31
    · exact floorProof32
    · exact floorProof33
    · exact floorProof34
    · exact floorProof35
    · exact floorProof36
    · exact floorProof37
    · exact floorProof38
    · exact floorProof39
    · exact floorProof40
def receipt (i : ℕ) : ℕ×ℕ := (if i<78 then (if i<39 then (if i<19 then (if i<9 then (if i<4 then (if i<2 then (if i<1 then (0,0) else (8,0)) else (if i<3 then (16,0) else (40,0))) else (if i<6 then (if i<5 then (37,0) else (5,0)) else (if i<7 then (1,0) else (if i<8 then (2,0) else (7,454))))) else (if i<14 then (if i<11 then (if i<10 then (0,474) else (3,0)) else (if i<12 then (6,474) else (if i<13 then (4,454) else (7,0)))) else (if i<16 then (if i<15 then (6,0) else (4,0)) else (if i<17 then (30,0) else (if i<18 then (33,0) else (5,454)))))) else (if i<29 then (if i<24 then (if i<21 then (if i<20 then (5,474) else (17,0)) else (if i<22 then (9,0) else (if i<23 then (7,74) else (6,394)))) else (if i<26 then (if i<25 then (0,394) else (1,2146694)) else (if i<27 then (4,74) else (if i<28 then (0,458) else (1,390))))) else (if i<34 then (if i<31 then (if i<30 then (6,398) else (18,0)) else (if i<32 then (0,398) else (if i<33 then (10,0) else (4,78)))) else (if i<36 then (if i<35 then (7,78) else (11,0)) else (if i<37 then (23,0) else (if i<38 then (20,0) else (0,462))))))) else (if i<58 then (if i<48 then (if i<43 then (if i<41 then (if i<40 then (6,458) else (1,454)) else (if i<42 then (2,454) else (26,0))) else (if i<45 then (if i<44 then (3,458) else (35,0)) else (if i<46 then (3,394) else (if i<47 then (6,462) else (6,142))))) else (if i<53 then (if i<50 then (if i<49 then (38,0) else (3,142)) else (if i<51 then (3,398) else (if i<52 then (6,466) else (21,0)))) else (if i<55 then (if i<54 then (0,466) else (12,0)) else (if i<56 then (3,466) else (if i<57 then (31,0) else (0,146)))))) else (if i<68 then (if i<63 then (if i<60 then (if i<59 then (3,146) else (13,0)) else (if i<61 then (36,0) else (if i<62 then (3,210) else (4,2195910)))) else (if i<65 then (if i<64 then (1,2195910) else (2,2195910)) else (if i<66 then (7,2195910) else (if i<67 then (3,474) else (0,414))))) else (if i<73 then (if i<70 then (if i<69 then (6,414) else (8,146)) else (if i<71 then (29,0) else (if i<72 then (6,146) else (2,74)))) else (if i<75 then (if i<74 then (0,210) else (5,464)) else (if i<76 then (24,0) else (if i<77 then (4,458) else (7,458)))))))) else (if i<117 then (if i<97 then (if i<87 then (if i<82 then (if i<80 then (if i<79 then (7,134) else (4,134)) else (if i<81 then (7,142) else (14,0))) else (if i<84 then (if i<83 then (4,334) else (4,462)) else (if i<85 then (19,0) else (if i<86 then (4,150) else (7,150))))) else (if i<92 then (if i<89 then (if i<88 then (22,0) else (4,470)) else (if i<90 then (25,0) else (if i<91 then (1,458) else (8,144)))) else (if i<94 then (if i<93 then (0,2163146) else (4,2163146)) else (if i<95 then (2,2163146) else (if i<96 then (3,2163146) else (7,2163146)))))) else (if i<107 then (if i<102 then (if i<99 then (if i<98 then (6,2163146) else (2,458)) else (if i<100 then (1,146) else (if i<101 then (1,82) else (15,0)))) else (if i<104 then (if i<103 then (1,338) else (8,150)) else (if i<105 then (1,150) else (if i<106 then (1,406) else (1,474))))) else (if i<112 then (if i<109 then (if i<108 then (8,266) else (8,330)) else (if i<110 then (2,470) else (if i<111 then (39,0) else (27,0)))) else (if i<114 then (if i<113 then (6,202) else (4,2146382)) else (if i<115 then (2,78) else (if i<116 then (6,210) else (2,142))))))) else (if i<136 then (if i<126 then (if i<121 then (if i<119 then (if i<118 then (7,334) else (2,1978702)) else (if i<120 then (2,334) else (7,462))) else (if i<123 then (if i<122 then (32,0) else (4,198)) else (if i<124 then (7,198) else (if i<125 then (7,202) else (0,2146702))))) else (if i<131 then (if i<128 then (if i<127 then (4,214) else (7,214)) else (if i<129 then (8,203) else (if i<130 then (28,0) else (6,266)))) else (if i<133 then (if i<132 then (0,266) else (0,270)) else (if i<134 then (6,270) else (if i<135 then (0,1716370) else (1,1716370)))))) else (if i<146 then (if i<141 then (if i<138 then (if i<137 then (3,1716370) else (6,1716370)) else (if i<139 then (2,150) else (if i<140 then (3,1978578) else (34,0)))) else (if i<143 then (if i<142 then (7,470) else (1,1978706)) else (if i<144 then (3,270) else (if i<145 then (4,405654) else (1,405654))))) else (if i<151 then (if i<148 then (if i<147 then (2,405654) else (7,405654)) else (if i<149 then (4,330) else (if i<150 then (7,330) else (0,2179546)))) else (if i<153 then (if i<152 then (1,2179546) else (3,2179546)) else (if i<154 then (6,2179546) else (if i<155 then (4,94) else (7,94)))))))))
def database : Memo := fun i => (floorLibrary.getD (receipt i).1 emptyFloor,(receipt i).2)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem certifiedDB : Certified 87 database := fun i => storedFloor (receipt i).1

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc0 : Excluded 87 9 s00 := offAudit (g:=(.saved 0)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b1x0 : Block 87 8 (successors 87 8 s01) 0 10 := offMemoRows (code:=0x40f400001401402001001001402401) (gs:=[(.fork 0x40c40b09240b00040a40b40b40a40a40940808a408000407408408407407000406052406000022000405022405404404403403402402 []),(.fork 0x8440e08440d404409403402402401 []),(.fork 0x40241140240a41140a40241040240741040740240240640640200000040640240240240240540205240540f40040040f40040f40f40004a402 []),(.fork 0x4405240440240108a04a04a [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b1x1 : Block 87 8 (successors 87 8 s01) 10 10 := offMemoRows (code:=0x40040040f400400400400400400400) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b1x2 : Block 87 8 (successors 87 8 s01) 20 10 := offMemoRows (code:=0x140f400400400400400400400001) (gs:=[(.fork 0x40e40e40e40e40e40e09240e40e40e40e40840c40840840840801200040c00041241202301205205240040040c00040440f40440f40f40140240140240140140f40140f40f400400 []),(.fork 0x40b40940b40b40b40b40d40d40d40d40d40d09240d40d40d40d01200040900041341302301209209240f40f40900040340040340040040140240140240140140040140040040f40f [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b1x3 : Block 87 8 (successors 87 8 s01) 30 10 := offMemoRows (code:=0x140500100140240540f40f40f40f) (gs:=[(.fork 0x41740a41740a416407416407000406032406415415414414402402401000022401 []),(.fork 0x415418414405402402 []),(.fork 0x41540240504a02a000 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b1x4 : Block 87 8 (successors 87 8 s01) 40 10 := offMemoRows (code:=0x140f400400400400001400402001) (gs:=[(.fork 0x40240a41140a40240741040741941940240600440640040f40040f40f40040f400000022402402402402402000401402052401 []),(.fork 0x40e40e40e40e40e40e41641a41641600003241a00040040041a01240240540240540540040005205240f41540f41540f40f40540f40540f []),(.fork 0x41741841741740d40d40d40d40d40d00005241800040f40f41440041440040040540040540040041801240240540240540540f40f092092 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b1x5 : Block 87 8 (successors 87 8 s01) 50 10 := offMemoRows (code:=0x40240600100100108b40f40f40f40f) (gs:=[(.fork 0x4a41c01240f09241b012400052401022025402022402022405047 []),(.fork 0x41500040504740e08a40d08a40f092400052402405052405 []),(.fork 0x2440f092404024400052401000401402052401048 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b1x6 : Block 87 8 (successors 87 8 s01) 60 10 := offMemoRows (code:=0x40040040040040200141c406001001) (gs:=[(.fork 0x41d41f41d40a41d40a42242141c42242240742240742105241f03203200000040503200040540542100042042041f00041e41e05241c41c41d41c032402402401006052401 []),(.fork 0x2600042041f41e406402402 []),(.fork 0x41140240240a41140a41040240240741040740200040200040240500040540201240040640040640201240f40040f40040240240240240241c401402000401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b1x7 : Block 87 8 (successors 87 8 s01) 70 10 := offMemoRows (code:=0x40e40e00141c00141c40f40f40f40f) (gs:=[(.fork 0x42440603241c402423032423 []),(.fork 0x41541c40f052400032402405000405 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b1x8 : Block 87 8 (successors 87 8 s01) 80 10 := offMemoRows (code:=0x40d40d40d40700141c00141c40e40e) (gs:=[(.fork 0x42642540205240241c []),(.fork 0x40f09240440005240140205240140605241c [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b1x9 : Block 87 8 (successors 87 8 s01) 90 10 := offMemoRows (code:=0x40040040040040d40040d40d40d407) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b1x10 : Block 87 8 (successors 87 8 s01) 100 10 := offMemoRows (code:=0x40d40d40d40d40f40f40d40f40f40f) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b1x11 : Block 87 8 (successors 87 8 s01) 110 10 := offMemoRows (code:=0x40d40d40e40e40e40e40d40d40d40d) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b1x12 : Block 87 8 (successors 87 8 s01) 120 10 := offMemoRows (code:=0x40e40e40e40a40e40e40e40a40d40d) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b1x13 : Block 87 8 (successors 87 8 s01) 130 10 := offMemoRows (code:=0x40f40f40e40f40040040e400400400) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b1x14 : Block 87 8 (successors 87 8 s01) 140 10 := offMemoRows (code:=0x40e40e40e40e40e40e40e40e40f40f) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc1 : Excluded 87 9 s01 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=10) (q:=15) (by decide) (by decide +kernel)
  intro j;fin_cases j
  · exact b1x0
  · exact b1x1
  · exact b1x2
  · exact b1x3
  · exact b1x4
  · exact b1x5
  · exact b1x6
  · exact b1x7
  · exact b1x8
  · exact b1x9
  · exact b1x10
  · exact b1x11
  · exact b1x12
  · exact b1x13
  · exact b1x14

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc2 : Excluded 87 9 s02 := offAudit (g:=(.saved 0)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc4 : Excluded 87 9 s04 := offAudit (g:=(.saved 0)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b5x0 : Block 87 8 (successors 87 8 s05) 0 10 := offMemoRows (code:=0x401400400400400400400400401400) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b5x1 : Block 87 8 (successors 87 8 s05) 10 10 := offMemoRows (code:=0x400400400400400400400001400400) (gs:=[(.fork 0x40e40e08a40e40e40e40e40e40e40e40e40840840840c40840800600002300a04a04a40c00041241240040040c00040440f40440f40f40040040140240140240140140f40140f40f [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b5x2 : Block 87 8 (successors 87 8 s05) 20 10 := offMemoRows (code:=0x400400404001001405001001404405) (gs:=[(.fork 0x40f02240f42742702242700040a42742740a40a00040702240741b00404a00000040604a00340640641541541b04400741b41241b404404 []),(.fork 0x2242700740e04642841541b005405404404 []),(.fork 0x2e42a41540440540e0c242904a04a022012 []),(.fork 0x40440f00040f40440a40440a404407000407404047404406000406404044401404400404401401400404404404412022404404404012405400400405 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b5x3 : Block 87 8 (successors 87 8 s05) 30 10 := offMemoRows (code:=0x401001001001001401400400001400) (gs:=[(.fork 0x40e40e00a40e40e40e40e40e40e40e40e412082412082400400412412404412022412404412022401412401412401401412401412401400400 []),(.fork 0x2241b42702242742742742742741b02200004241b04408204204205204204341b00440140100740041b40040041241b404405404405405401401400405400405400 []),(.fork 0x2242b04a42840140100540040440540140140040541b400 []),(.fork 0x3642a40140440540140e0c2429052400022400405012400042 []),(.fork 0x40400040140140440442c42c401404404026404048404000404026401401401400400401400412404405405401042415401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b5x4 : Block 87 8 (successors 87 8 s05) 40 10 := offMemoRows (code:=0x42840600100140440640c00100140c) (gs:=[(.fork 0x4442d41800000540040c404414022414 []),(.fork 0x4c42a41540c40108241240040440508a405 []),(.fork 0x40f04440f00642e00040a42e42e40a40a42804a00040704a40700004200040504a40542042042542542842e404404404404 []),(.fork 0x642e00740e420426425406404404 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b5x5 : Block 87 8 (successors 87 8 s05) 50 10 := offMemoRows (code:=0x1401400400400400001400404001) (gs:=[(.fork 0x40440f08a40f40440a40440a40440700040740408240440504a40540040640040640140040140042804404c428404404404404404428 []),(.fork 0x40e40e00a40e40e40e40e40e40e42800004704204b04a04700a41241240040040e40e428001404404404406404406406400400006000401420401420401401406401406406 [(.fork 0x42f022412423400 [])]),(.fork 0x44430401425400406400426400404406401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b5x6 : Block 87 8 (successors 87 8 s05) 60 10 := offMemoRows (code:=0x40e40e40e40e001428001428401428) (gs:=[(.fork 0x1443142405200142800740040442304a423 [(.fork 0x42f022412423400 [])]),(.fork 0x1842a41504204e40642840105241240040440504a405 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b5x7 : Block 87 8 (successors 87 8 s05) 70 10 := offMemoRows (code:=0x42940700100140440740c428001428) (gs:=[(.fork 0x4443241f40000004640642840441e04641e []),(.fork 0x40840f40840f04243300040a43343340a40a00040604a406000405022405436436435408434434429433404404 []),(.fork 0x4243300740e436435434407404404 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b5x8 : Block 87 8 (successors 87 8 s05) 80 10 := offMemoRows (code:=0x1401400400400400001400404001) (gs:=[(.fork 0x40440f40840f40440a40440a404406000406404405022405400407400407404408401400401400408429429016404404404404404429 []),(.fork 0x40840840e40e08240e40e40e00004202302241241240040040e40e429042404407404407407400400408408401436401436401401407401407407 []),(.fork 0x44437401434400404407401400407435400 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b5x9 : Block 87 8 (successors 87 8 s05) 90 10 := offMemoRows (code:=0x428429001428001429001429401429) (gs:=[(.fork 0x8443a43904204201340742908a40c007400404438022438 []),(.fork 0x5a42a41500042940105241240040440504a405 []),(.fork 0x2443d43c00040604a42805240140004240443b04a43b [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b5x10 : Block 87 8 (successors 87 8 s05) 100 10 := offMemoRows (code:=0x40a40a40c42940842940e40e40e40e) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b5x11 : Block 87 8 (successors 87 8 s05) 110 10 := offMemoRows (code:=0x40e00140e00140e40a40e40e40e40e) (gs:=[(.fork 0x42c43e08342c42c43e08442c43e44044144043f44002343f05644008344042c44004342c40e40e40e40e42c44008442c43e43f04343f01543f01343f42c43f04342c40e40e40e40e42c43f00442c43e04704343e42c03402242c40e40e40e40e42c02c02242c40e40e40e40e40e40e40e40e40e40e40e40e40e40e40e40e []),(.fork 0x42c43e08442c40e08242c44004242c40e00442c43f00442c42c02200440e42c02c02242c40e40e40e40e40e08442c40e40e40e40e42c40e42c40e40e40e40a [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b5x12 : Block 87 8 (successors 87 8 s05) 120 10 := offMemoRows (code:=0x40e40e40e40e40040040040040e400) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b5x13 : Block 87 8 (successors 87 8 s05) 130 10 := offMemoRows (code:=0x40e40e40e40e40e40e40e40e40e40e) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b5x14 : Block 87 8 (successors 87 8 s05) 140 10 := offMemoRows (code:=0x140140400140c40f00100140440f) (gs:=[(.fork 0x40c40b08640b00040a40b40b40a40a40940808a408000407408408407407000406046406000022000405022405402402403403404404 []),(.fork 0x8640b00740e08642940240940340f404404 []),(.fork 0x40440a40440a40440840440740840740440600040640400040440500040540440440440440f40040040f40040140140040c404 []),(.fork 0x8444208a42940100040340040f40040940040440f401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b5x15 : Block 87 8 (successors 87 8 s05) 150 10 := offMemoRows (code:=0x40140c) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc5 : Excluded 87 9 s05 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=10) (q:=16) (by decide) (by decide +kernel)
  intro j;fin_cases j
  · exact b5x0
  · exact b5x1
  · exact b5x2
  · exact b5x3
  · exact b5x4
  · exact b5x5
  · exact b5x6
  · exact b5x7
  · exact b5x8
  · exact b5x9
  · exact b5x10
  · exact b5x11
  · exact b5x12
  · exact b5x13
  · exact b5x14
  · exact b5x15

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc6 : Excluded 87 9 s06 := offAudit (g:=(.saved 0)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b7x0 : Block 87 8 (successors 87 8 s07) 0 10 := offMemoRows (code:=0x40100140140f400400400400400401) (gs:=[(.fork 0x40344440340a44440a40340340340740340740300440340600040640100002440340340504640540140140344340340044340040140140140140040f40f400 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b7x1 : Block 87 8 (successors 87 8 s07) 10 10 := offMemoRows (code:=0x40040040040140040040140f401401) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b7x2 : Block 87 8 (successors 87 8 s07) 20 10 := offMemoRows (code:=0x401001401405400400400400400400) (gs:=[(.fork 0x42742742740a42740a00008400040708440700000400040600040640340340140141b41b40140140f02704440f40040540540040041b41b400 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b7x3 : Block 87 8 (successors 87 8 s07) 30 10 := offMemoRows (code:=0x1401400400400400401401401405) (gs:=[(.fork 0x42742742742700000040100000000000000040040040100041b401415401405405401401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b7x4 : Block 87 8 (successors 87 8 s07) 40 10 := offMemoRows (code:=0x40140640300c001403401401401401) (gs:=[(.fork 0x418414401046401403 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b7x5 : Block 87 8 (successors 87 8 s07) 50 10 := offMemoRows (code:=0x400400400400401401401406401001) (gs:=[(.fork 0x42540a43040a42543c42540743c40740100042540500040540140142543040140142542640140140f42500040f400406406400400425426400 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b7x6 : Block 87 8 (successors 87 8 s07) 60 10 := offMemoRows (code:=0x40e40e00e425001425401401401401) (gs:=[(.fork 0x424000405006425401423000401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b7x7 : Block 87 8 (successors 87 8 s07) 70 10 := offMemoRows (code:=0x40100140140740342500142540e40e) (gs:=[(.fork 0x41f40f00641e401000401425 []),(.fork 0x43440a43340a43440643c40643440508640540140143443343443c40140143443540140140f43440340f400407407400400434435400 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b7x8 : Block 87 8 (successors 87 8 s07) 80 10 := offMemoRows (code:=0x401401400400400400401401401407) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b7x9 : Block 87 8 (successors 87 8 s07) 90 10 := offMemoRows (code:=0x42543443c42500e434001434401401) (gs:=[(.fork 0x439000405086445407434064403401438084401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b7x10 : Block 87 8 (successors 87 8 s07) 100 10 := offMemoRows (code:=0x40e40a40343440343440e40e40e40e) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b7x11 : Block 87 8 (successors 87 8 s07) 110 10 := offMemoRows (code:=0x40040040040040e40e40e40a40e40e) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b7x12 : Block 87 8 (successors 87 8 s07) 120 10 := offMemoRows (code:=0x40e40e40e40e40e40e40e40e40e40e) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b7x13 : Block 87 8 (successors 87 8 s07) 130 10 := offMemoRows (code:=0x40140140140140e40e40e40e) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc7 : Excluded 87 9 s07 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=10) (q:=14) (by decide) (by decide +kernel)
  intro j;fin_cases j
  · exact b7x0
  · exact b7x1
  · exact b7x2
  · exact b7x3
  · exact b7x4
  · exact b7x5
  · exact b7x6
  · exact b7x7
  · exact b7x8
  · exact b7x9
  · exact b7x10
  · exact b7x11
  · exact b7x12
  · exact b7x13

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc8 : Excluded 87 9 s08 := offAudit (g:=(.saved 0)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b9x0 : Block 87 8 (successors 87 8 s09) 0 10 := offMemoRows (code:=0x41540141a40f41500100100141540f) (gs:=[(.fork 0x41740a41740a416407416407000406026406414414402402415415401000022401 []),(.fork 0x41441840241541540f []),(.fork 0x41540a42a40a41641a41540741640741540642440641541541541540040f40040f41a00e40141502240140040540540041a415 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b9x1 : Block 87 8 (successors 87 8 s09) 10 10 := offMemoRows (code:=0x400400400400143401415001001001) (gs:=[(.fork 0x40f02240f42742702242700040a42742740a40a00040702240741b00405200000040605200340640641b04400b41b41241b404404415415 []),(.fork 0x2440e04442441200b41b404415415401 []),(.fork 0x41542a41540700040741542441504441541541541541541540f41500040f40a41542a40a406415424406400405405400405400400405012415 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b9x2 : Block 87 8 (successors 87 8 s09) 20 10 := offMemoRows (code:=0x405001405400400400405400400400) (gs:=[(.fork 0x1241440041540f40f400418400405405 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b9x3 : Block 87 8 (successors 87 8 s09) 30 10 := offMemoRows (code:=0x140040040540000140500140541a) (gs:=[(.fork 0x4a42400540041540140140041b400405405 []),(.fork 0x41a0924000a2415401401400012400405405 []),(.fork 0x40e40e40e40e40e40e41641641641a00002640040041a01240240540240540504a04a40f41540f41540f40f40540f40540f41a000400400 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b9x4 : Block 87 8 (successors 87 8 s09) 40 10 := offMemoRows (code:=0x415406400400400400400400400400) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b9x5 : Block 87 8 (successors 87 8 s09) 50 10 := offMemoRows (code:=0x405424424405415001424406424001) (gs:=[(.fork 0x42440a42f40a42440704440742342342042041541540142405240140f42402440f []),(.fork 0x41540a42a40a42404441540704b40740540040540040040640040605442442442a41541541541541542440141505240140f41500040f [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b9x6 : Block 87 8 (successors 87 8 s09) 60 10 := offMemoRows (code:=0x40e40e40e40e400400400400001400) (gs:=[(.fork 0x40e40e40e40e42404440040042040542040540542400a0a242440e40e424424415406415406406400400424024405406405406406 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b9x7 : Block 87 8 (successors 87 8 s09) 70 10 := offMemoRows (code:=0x41540700142400142441a424001424) (gs:=[(.fork 0x40002644641e415026415424 []),(.fork 0x426425415052415424 []),(.fork 0x4044014150524010a2056406424 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b9x8 : Block 87 8 (successors 87 8 s09) 80 10 := offMemoRows (code:=0x405448001405415001448407001001) (gs:=[(.fork 0x44740a44740a00040604640643941643843843643644844741541540100002240140f41602200041640f41640f []),(.fork 0x43843943640741541502641a []),(.fork 0x41540a42a40a41540642440641541640540040540040040740040741541541541541544840141500040140f41541640f []),(.fork 0x40541540740502a41a438400400407439400 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b9x9 : Block 87 8 (successors 87 8 s09) 90 10 := offMemoRows (code:=0x40e40e424448001424400400400400) (gs:=[(.fork 0x44904604640642441543b044415 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b9x10 : Block 87 8 (successors 87 8 s09) 100 10 := offMemoRows (code:=0x144800144841a44841644840e40e) (gs:=[(.fork 0x435434415022415448 []),(.fork 0x404401415052401448 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b9x11 : Block 87 8 (successors 87 8 s09) 110 10 := offMemoRows (code:=0x40e40540e40e40e40a40e40e40e40a) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b9x12 : Block 87 8 (successors 87 8 s09) 120 10 := offMemoRows (code:=0x40e40e40040040040040540e40e40e) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b9x13 : Block 87 8 (successors 87 8 s09) 130 10 := offMemoRows (code:=0x141a00141a40e40e40e40e40e40e) (gs:=[(.fork 0x4a44800040900b40f40341502241541a []),(.fork 0x40441a415401092401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc9 : Excluded 87 9 s09 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=10) (q:=14) (by decide) (by decide +kernel)
  intro j;fin_cases j
  · exact b9x0
  · exact b9x1
  · exact b9x2
  · exact b9x3
  · exact b9x4
  · exact b9x5
  · exact b9x6
  · exact b9x7
  · exact b9x8
  · exact b9x9
  · exact b9x10
  · exact b9x11
  · exact b9x12
  · exact b9x13

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b10x0 : Block 87 8 (successors 87 8 s10) 0 10 := offMemoRows (code:=0x40500140540f400400405400400400) (gs:=[(.fork 0x41741841440a41740a41440743840741444641440644640641802241441841440041840040540540540540f40040f400405405401414046401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b10x1 : Block 87 8 (successors 87 8 s10) 10 10 := offMemoRows (code:=0x40540540500140540540540f405405) (gs:=[(.fork 0x4200040f04440f40542742740a42740a0004070844070a20040a200000040600400340640641b41b41b40041b400405405405400405400405405 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b10x2 : Block 87 8 (successors 87 8 s10) 20 10 := offMemoRows (code:=0x400400400400400405400400405401) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b10x3 : Block 87 8 (successors 87 8 s10) 30 10 := offMemoRows (code:=0x400400405405405405405405405405) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b10x4 : Block 87 8 (successors 87 8 s10) 40 10 := offMemoRows (code:=0x405406400400400400001400400400) (gs:=[(.fork 0x40e40e40e40e40e40e01240e40e40e40e412082412082412412404412022412404412022400400401412401412401401412401412401400400 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b10x5 : Block 87 8 (successors 87 8 s10) 50 10 := offMemoRows (code:=0x405405405405405405405406405001) (gs:=[(.fork 0x42f42442340a42f40a42340704440742408240540540640040640042344642342440540540540540142300640140f42344640f400423424400 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b10x6 : Block 87 8 (successors 87 8 s10) 60 10 := offMemoRows (code:=0x44642340e40e40e40e400400400400) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b10x7 : Block 87 8 (successors 87 8 s10) 70 10 := offMemoRows (code:=0x405001405407001423001423414423) (gs:=[(.fork 0x426401006425405004405423 []),(.fork 0x4000124044010a240140500440544a406423 []),(.fork 0x43840a44740a43840604640643908240740040740000443843843843844743800443843940540540540540143808640140f43844b02a43840f44b40f400438439400 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b10x8 : Block 87 8 (successors 87 8 s10) 80 10 := offMemoRows (code:=0x400400405405405405405405405407) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b10x9 : Block 87 8 (successors 87 8 s10) 90 10 := offMemoRows (code:=0x40e40e40e40e423438001423400400) (gs:=[(.fork 0x44943840640700642340543b044405 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b10x10 : Block 87 8 (successors 87 8 s10) 100 10 := offMemoRows (code:=0x40540a001438001438414438438414) (gs:=[(.fork 0x435434405084405438 []),(.fork 0x400012404401405022405407006438 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b10x11 : Block 87 8 (successors 87 8 s10) 110 10 := offMemoRows (code:=0x40540540e40540540540540a40540e) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b10x12 : Block 87 8 (successors 87 8 s10) 120 10 := offMemoRows (code:=0x40e40e40040040e400400400405405) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b10x13 : Block 87 8 (successors 87 8 s10) 130 10 := offMemoRows (code:=0x1341400141440e40e40e40e40e40e) (gs:=[(.fork 0x5443840940104241340f403405044405414 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc10 : Excluded 87 9 s10 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=10) (q:=14) (by decide) (by decide +kernel)
  intro j;fin_cases j
  · exact b10x0
  · exact b10x1
  · exact b10x2
  · exact b10x3
  · exact b10x4
  · exact b10x5
  · exact b10x6
  · exact b10x7
  · exact b10x8
  · exact b10x9
  · exact b10x10
  · exact b10x11
  · exact b10x12
  · exact b10x13

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc11 : Excluded 87 9 s11 := offAudit (g:=(.saved 0)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b16x0 : Block 87 8 (successors 87 8 s16) 0 10 := offMemoRows (code:=0x405001405400405401405405405405) (gs:=[(.fork 0x41542a41540a42a40a41504741540700040741542441540642440640540540540540040540040541504740140140540540f41500040f401400400401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b16x1 : Block 87 8 (successors 87 8 s16) 10 10 := offMemoRows (code:=0x40540540500140540f405400405405) (gs:=[(.fork 0x41402741440a00040a41443841440743840741444641440644640641404741440000040040540540540540f40540f40540140140540540140f40f401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b16x2 : Block 87 8 (successors 87 8 s16) 20 10 := offMemoRows (code:=0x40540540540540540140500140540f) (gs:=[(.fork 0x2b41404c41441445703341441545742a41540540540540501c45701c45741443443841445743403343442343443c42341543403341540540540540502b43408c43441442344642345742343042341542342441540540540540502b40500c02e42300c42300741441505341501b41504c415405405405405405405405405405001405001 [(.fork 0x1541403341441445703341441545742a41500d45701b45741443443841445743403343442343443c42341543403341501543405343441442344642345742343042341542342441500d42302b42341441503341500d41502b415 []),(.fork 0x41403441400045701c45700043405443402a00000042302c02b42300f02b02b00041502c415405405 [])])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b16x3 : Block 87 8 (successors 87 8 s16) 30 10 := offMemoRows (code:=0x401401405405405405405405405405) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b16x4 : Block 87 8 (successors 87 8 s16) 40 10 := offMemoRows (code:=0x40500140540641441508b415401401) (gs:=[(.fork 0x42340a43040a42343c42340743c40740540540140502c40640540640542344642343042342440140140540540540540f42344640f400423424400401406406401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b16x5 : Block 87 8 (successors 87 8 s16) 50 10 := offMemoRows (code:=0x401401405405405405405405405406) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b16x6 : Block 87 8 (successors 87 8 s16) 60 10 := offMemoRows (code:=0x457423430423415423424415401401) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b16x7 : Block 87 8 (successors 87 8 s16) 70 10 := offMemoRows (code:=0x405407405001405407414423446423) (gs:=[(.fork 0x43440a00040a43440643c40640540140740540740543443843402743443c43404740140140540540540540f43443840f400434000400401407407401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b16x8 : Block 87 8 (successors 87 8 s16) 80 10 := offMemoRows (code:=0x401401401401405405405405405405) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b16x9 : Block 87 8 (successors 87 8 s16) 90 10 := offMemoRows (code:=0x4b43442343443c42341543408b415) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b16x10 : Block 87 8 (successors 87 8 s16) 100 10 := offMemoRows (code:=0x40500140540a414434438414457434) (gs:=[(.fork 0x45702745740700040745743045740643040640540140a40540a40545702745742a40140140540540540540f45700040f40045742a40040140a40a401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b16x11 : Block 87 8 (successors 87 8 s16) 110 10 := offMemoRows (code:=0x40140140540540540540540540540a) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b16x12 : Block 87 8 (successors 87 8 s16) 120 10 := offMemoRows (code:=0x41445704b41441545742a415401401) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b16x13 : Block 87 8 (successors 87 8 s16) 130 10 := offMemoRows (code:=0x401401401401) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc16 : Excluded 87 9 s16 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=10) (q:=14) (by decide) (by decide +kernel)
  intro j;fin_cases j
  · exact b16x0
  · exact b16x1
  · exact b16x2
  · exact b16x3
  · exact b16x4
  · exact b16x5
  · exact b16x6
  · exact b16x7
  · exact b16x8
  · exact b16x9
  · exact b16x10
  · exact b16x11
  · exact b16x12
  · exact b16x13

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b17x0 : Block 87 8 (successors 87 8 s17) 0 10 := offMemoRows (code:=0x401405405405401405001401401401) (gs:=[(.fork 0x2b41404c41441445702b41441545742a41501c45701c45740540540540541443443841445743402b43442343443c42341543402b41502b43408c43440540540540541442344642345742343042341542342441500c02e42300c42300740540540540502b40541441504b41501b41504c415405405405405405405405405405001405001 [(.fork 0x1541403341441445703341441545742a41500d45701b45741443443841445743403343442343443c42341543403341501543405343441442344642345742343042341542342441500d42302b42341441503341500d41502b415 []),(.fork 0x41403441400045701c45700043405443402a00000042302c02b42300f02b02b00041502c415405405 [])])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b17x1 : Block 87 8 (successors 87 8 s17) 10 10 := offMemoRows (code:=0x40544c40500140541b405001405401) (gs:=[(.fork 0x4442400740040540541540140140041b400 []),(.fork 0x4444600740f40540541440140140f44c40f [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b17x2 : Block 87 8 (successors 87 8 s17) 20 10 := offMemoRows (code:=0x100141b40000100141b400405405) (gs:=[(.fork 0x40f02240f42742702242700040a42742740a40a00040702240741b00404600000040604600340640641541541241b40440441b04400741b []),(.fork 0x2242b04600304445a41504740440000741b []),(.fork 0x42742742741b42740a42740a00040708440700040600040641b00840140040140041b00e40f02b00040f40040540540041b008 []),(.fork 0x1500c41b008405401400 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b17x3 : Block 87 8 (successors 87 8 s17) 30 10 := offMemoRows (code:=0x44c41b00141b40100141b001001401) (gs:=[(.fork 0x2242742742742741b42702242700004241b02204204a04204341b04408204240140141241b40440540440540540040540040540041b00400b40041b400400401401 []),(.fork 0x2242b04442840140140440540040541b40000b400401401 []),(.fork 0x42742742742700000000000000000040100040140140540540040040100041540141b401 []),(.fork 0x4441c04502240500640f08600640004641b40102202b402022402 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b17x4 : Block 87 8 (successors 87 8 s17) 40 10 := offMemoRows (code:=0x100145a40600100145a001406406) (gs:=[(.fork 0x4600041e00641e00002600045100645100008600043b00643b00004600042000642042342342542342542300542542545a45a45a45a45a45a45a45a45a45a45a45a05245a000 []),(.fork 0x40f04440f00040a02440a00040708440700040004440042342342542505245a000 []),(.fork 0x42300742540605245a052 []),(.fork 0x45b45d04345b04445d04445d45d45f04345f45c45f46145c45b45f02345b44a45f02344a02445f02445f45d45e46045e45f45e04345e45c45e04345c45b45e08345b44a45e08344a08445e08445e45d45c04345c45b45c04345b04445c04445c44a45a05245b45d44a04344a45c44a04344a45b44a05244a45b45a05244a []),(.fork 0x40f04440f00040a02440a45a45e08445a00040708440700040004440040540640540640140640140645d45a04445a45f45a02445a45c45a04445a45b45a05245a44a45a05245a05245a [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b17x5 : Block 87 8 (successors 87 8 s17) 50 10 := offMemoRows (code:=0x140140500145a001001405001001) (gs:=[(.fork 0x4200045d04445d00002200045f02445f00008200045e08445e00004200045c04445c44a44a44a05245b44a45b44a02b45b45b45b05245a45a406 []),(.fork 0x40540100740140505205205205245a05245a406 []),(.fork 0x4400002200008200004440540545a04445a04445a45a05240645a406406405405401423401423401401406401406406 []),(.fork 0x40540505240640540542340140140645a406 []),(.fork 0x4240502245a08440508200004240540545a02445b45a02a45a45a05240645a40640640545a401405405405405425405 []),(.fork 0x4200002400008445a08400004240140142540542540540540640540640540645a02445a45a05240645a406406401401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b17x6 : Block 87 8 (successors 87 8 s17) 60 10 := offMemoRows (code:=0x145a41b45a00141b40100145a001) (gs:=[(.fork 0x40140142540540640545a406052406401401 []),(.fork 0x40104200002200008240104240140140140540140540545a04445a04444a45a02a45a45a05240645a40640640145a423401 []),(.fork 0x42404640000604604604640641b401042000420046420 []),(.fork 0x43002640a00602602602640645a405022000451026451 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b17x7 : Block 87 8 (successors 87 8 s17) 70 10 := offMemoRows (code:=0x100146240744c45a00145a42b45a) (gs:=[(.fork 0x44604640f00604604604640645a40104200041e04641e []),(.fork 0x44d44d04244d00040f44d44d40f40f00040a04240a08600000040608600340640600040002240043843843443446202446200444546200b462 []),(.fork 0x4244c08600308445a43808743440700b462 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b17x8 : Block 87 8 (successors 87 8 s17) 80 10 := offMemoRows (code:=0x405001462001001405001001462407) (gs:=[(.fork 0x44d44d44d40f44d40f05340a00040a00040600040600040004440040540740540740140740140744d46246200846200e00c462 []),(.fork 0x2540140500c46200c407 []),(.fork 0x44d44d44d44d00004208208a08208304208200004240540546244d46200446208446202244546200b40746240740740540504244d401438401438401401407401407407 []),(.fork 0x8446340540500b40740540504244c438401401407462407 []),(.fork 0x44d44d44d44d405000000000000000405000000000405405407407405462401405434405 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b17x9 : Block 87 8 (successors 87 8 s17) 90 10 := offMemoRows (code:=0x145a41b46200141b401462001401) (gs:=[(.fork 0x8443c401434405407405462407007407401 []),(.fork 0x4446402502202241b000436022436 []),(.fork 0x43c08608608640608640700645a40508200043b08443b [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b17x10 : Block 87 8 (successors 87 8 s17) 100 10 := offMemoRows (code:=0x44c46244d46242b46200146245a462) (gs:=[(.fork 0x4446602500640a086006407026462042401405042053465042465 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b17x11 : Block 87 8 (successors 87 8 s17) 110 10 := offMemoRows (code:=0x140500100142b40a00100142b40a) (gs:=[(.fork 0x40f04240f42b08400040704240742b00402600000040602600340640642742702242700040042742740040042a42a45745746742b00b42b []),(.fork 0x2600302445a02241b42a01745740a00b42b []),(.fork 0x40f08440f05340700040700040600040642742742740042740040540a40540a40140a40140a42742b42b00842b00e00c42b []),(.fork 0x1740140500c42b00c40a []),(.fork 0x2242b00400004202202a02202342b02404202242742742742740540542b04242b42746742b00b40a42b40a40a40540502242740142a40142a40140140a40140a40a [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b17x12 : Block 87 8 (successors 87 8 s17) 120 10 := offMemoRows (code:=0x42741b40142b00140140500142b001) (gs:=[(.fork 0x2446840540500b40a40540502241b42a40140140a42b40a []),(.fork 0x40500000000000000040500042742742742740540540a40a40542b401405457405 []),(.fork 0x2443040145740540a40542b40a00740a401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b17x13 : Block 87 8 (successors 87 8 s17) 130 10 := offMemoRows (code:=0x100144c40f44c42b00142b41b42b) (gs:=[(.fork 0x4446902504204242b000454042454 []),(.fork 0x40a04240a44d44d04244d00040744d44d40740744c00404600000040604600340640644c08400040002240041441441344c40340300744c []),(.fork 0x4246204600304445a41404740340f00744c [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b17x14 : Block 87 8 (successors 87 8 s17) 140 10 := offMemoRows (code:=0x40100144c00100140100100144c40f) (gs:=[(.fork 0x40a02440a44d44d44d44c44d40744d40700040600040644c00840140f40140f44c00e40002b00040040f40540540f44c008 []),(.fork 0x2500c44c00840540140f []),(.fork 0x2244c04244d44d44d44d44c44d04244d04204a04204344c04402204244c00400002240140141344c40340540340540540f40540f40540f00b40f44c40f40f401401 []),(.fork 0x4246204446a40140140340540f40544c40f00b40f401401 []),(.fork 0x44d44d44d44d00000000000040100040140140540540f40f40100041440144c401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc17 : Excluded 87 9 s17 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=10) (q:=15) (by decide) (by decide +kernel)
  intro j;fin_cases j
  · exact b17x0
  · exact b17x1
  · exact b17x2
  · exact b17x3
  · exact b17x4
  · exact b17x5
  · exact b17x6
  · exact b17x7
  · exact b17x8
  · exact b17x9
  · exact b17x10
  · exact b17x11
  · exact b17x12
  · exact b17x13
  · exact b17x14

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b18x0 : Block 87 8 (successors 87 8 s18) 0 10 := offMemoRows (code:=0x405001405400405001405405405405) (gs:=[(.fork 0x40104200040f02240f40501200040a02240a405082000407022407405052401052052000000406052003406406401042000400012400401405405405405401405405405 []),(.fork 0x40542a41540a42a40a41540700040741542441540642440640540540540540040540040541504441502240540540f41504440f400415012400 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b18x1 : Block 87 8 (successors 87 8 s18) 10 10 := offMemoRows (code:=0x405405405001405406405400405405) (gs:=[(.fork 0x42340700040740540542344642342442305240540540540540f42344640f40a42300040a400423424400406423052406405406406405 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b18x2 : Block 87 8 (successors 87 8 s18) 20 10 := offMemoRows (code:=0x405405405001405001405407405406) (gs:=[(.fork 0x46b4140a241441442a04341441542a42a41546b42a02442a40540540540541442344642342a42304342341542342441546b42300442340540540540541441508341546b41504441540540540540540540540540540540540540541443843841442a43802642a42343808342341543804641546b438022438405405405405 []),(.fork 0x41443843841442a43802442a42343808742341543804441546b43805243840540540540540540540f43843840f40a43802440a406438000406400438000400407438022407405407407405 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b18x3 : Block 87 8 (successors 87 8 s18) 30 10 := offMemoRows (code:=0x40500140500140540a405407405407) (gs:=[(.fork 0x46c41408441441443843841442343808342341543808341546c43808443840540540540542a43808442a41442344642341542342441546c42300442340540540540542a42302342341441508341546c4150c241540540540540540540540540540540540540541442a08641441542a42a41546c42a02242a405405405405 []),(.fork 0x42a43808442a42a40702640742a42302742342a40600040641442a08441441542a42a41546c42a0c242a40540540540540540540f42a00040f40042a42a40040a42a02240a40540a40a405 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b18x4 : Block 87 8 (successors 87 8 s18) 40 10 := offMemoRows (code:=0x40500140540f40540a40540a405405) (gs:=[(.fork 0x41440a00040a40543841440743840741444641440644640641408441440004640040540540540540f40540f40541404240540540f41402240f [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b18x5 : Block 87 8 (successors 87 8 s18) 50 10 := offMemoRows (code:=0x40500140540540540540540f405405) (gs:=[(.fork 0x40140140140140140141445702b41441545742a41540140140140141443443841445743403343442343443c42341543402b41540140140140141442344642345742343042341542342441540140140140141441504b415401401401401401401405405405405405405405405405405405405405405405405405405405405405405405405405401405001 [(.fork 0x1541403341441445703341441545742a41500d45701b45741443443841445743403343442343443c42341543403341501543405343441442344642345742343042341542342441500d42302b42341441503341500d41502b415 [])])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b18x6 : Block 87 8 (successors 87 8 s18) 60 10 := offMemoRows (code:=0x405405405405405405405405405401) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b18x7 : Block 87 8 (successors 87 8 s18) 70 10 := offMemoRows (code:=0x1405414415001415401415001401) (gs:=[(.fork 0x3442a40140440540e0c2429046042400022400405012400401 []),(.fork 0x4500040540e08440d08440f086400046402405046405415 []),(.fork 0x423000423000405405405405052405406406423405423446423424405405401401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b18x8 : Block 87 8 (successors 87 8 s18) 80 10 := offMemoRows (code:=0x424415401423001401405405405405) (gs:=[(.fork 0x40142540543000643c006052406052406405052406401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b18x9 : Block 87 8 (successors 87 8 s18) 90 10 := offMemoRows (code:=0x41442344642342a42304b423415423) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b18x10 : Block 87 8 (successors 87 8 s18) 100 10 := offMemoRows (code:=0x401438001401405405405405001405) (gs:=[(.fork 0x43800043800040543840540508240540740540740540743440543843843804a43808c43802a44543840540544b44b401401 []),(.fork 0x401434405437086407052407405022407401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b18x11 : Block 87 8 (successors 87 8 s18) 110 10 := offMemoRows (code:=0x142a42343810b423415438001415) (gs:=[(.fork 0x2540e08440704643640500040502a415 []),(.fork 0x3440a08640702646540502640504a04a42a405000 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b18x12 : Block 87 8 (successors 87 8 s18) 120 10 := offMemoRows (code:=0x40540500140541443843841442a438) (gs:=[(.fork 0x42a04a42a00042a02c42a00040540540542a01240540a40540a40540a45740542a04a42a42a46742a405405459459401401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b18x13 : Block 87 8 (successors 87 8 s18) 130 10 := offMemoRows (code:=0x41542a42a41540142a001401405405) (gs:=[(.fork 0x40145740546d02640a0c240a40502240a401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b18x14 : Block 87 8 (successors 87 8 s18) 140 10 := offMemoRows (code:=0x40141400140141442a001414) (gs:=[(.fork 0x2540d04440a08645440500040504a414 []),(.fork 0x5443840140340544208640d0a204240f04240f40502240f401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc18 : Excluded 87 9 s18 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=10) (q:=15) (by decide) (by decide +kernel)
  intro j;fin_cases j
  · exact b18x0
  · exact b18x1
  · exact b18x2
  · exact b18x3
  · exact b18x4
  · exact b18x5
  · exact b18x6
  · exact b18x7
  · exact b18x8
  · exact b18x9
  · exact b18x10
  · exact b18x11
  · exact b18x12
  · exact b18x13
  · exact b18x14

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc20 : Excluded 87 9 s20 := offAudit (g:=(.saved 0)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b21x0 : Block 87 8 (successors 87 8 s21) 0 10 := offMemoRows (code:=0x42040142140f42000100100142040f) (gs:=[(.fork 0x41d41f41d40a41d40a41c42242242142240742240741f02a42105202600000040502600040540541f00041e41e04a41c41c41d41c02a40240242100042042040100a046401 []),(.fork 0x4442441e41f40242042040f []),(.fork 0x46f42042040a46f40a42042242040742240742042442001242042000042042046f42042442042040040640040640142000a401405420424405400406406400421420 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b21x1 : Block 87 8 (successors 87 8 s21) 10 10 := offMemoRows (code:=0x400400400400001401420001001001) (gs:=[(.fork 0x40f04440f00a42e00040a42e42e40a40a42805200040705240700004200040505240542542542842e404404404404420420 []),(.fork 0x2440e425426404420420401 []),(.fork 0x42005242040700040742042042046f40442002642042040042040642040040040640f42000040f40a42046f40a40542042440540040640640004a420 []),(.fork 0x42504a42040100a04a [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b21x2 : Block 87 8 (successors 87 8 s21) 20 10 := offMemoRows (code:=0x406001406400400400406400400400) (gs:=[(.fork 0x42f42442442f424044424001406406424024424052424424420405420405405406406404424400423400423400400405400405400 [(.fork 0x42f412022400423 [])])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b21x3 : Block 87 8 (successors 87 8 s21) 30 10 := offMemoRows (code:=0x40640640640640640e406406406406) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b21x4 : Block 87 8 (successors 87 8 s21) 40 10 := offMemoRows (code:=0x400406001406406406406406406406) (gs:=[(.fork 0x4044044044044040004040a244a44a404052404052406406404404404400400404400000044404420026404420404400400404400406406 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b21x5 : Block 87 8 (successors 87 8 s21) 50 10 := offMemoRows (code:=0x400400001400400400400400400406) (gs:=[(.fork 0x40e40e40e40e01240e40e40e40e42800005304241241205305204b01240e40e428001400400404404404406404406406012000401420401420401401406401406406400400 [(.fork 0x42f412022400423 [])])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b21x6 : Block 87 8 (successors 87 8 s21) 60 10 := offMemoRows (code:=0x420001424405424001420405400400) (gs:=[(.fork 0x42440a47040a42440704440742342341541542042040142405240140f42402440f []),(.fork 0x42040a46f40a42404442040700040740640040640042042040040640040647142442042042042440142005240140f42002440f [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b21x7 : Block 87 8 (successors 87 8 s21) 70 10 := offMemoRows (code:=0x421424001424400400400400001400) (gs:=[(.fork 0x40e40e40e40e4240440a242440e40e400400424424415406415406406424024405406405406406420405420405405400400424012 []),(.fork 0x44640f052414420026420424 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b21x8 : Block 87 8 (successors 87 8 s21) 80 10 := offMemoRows (code:=0x47240700100142040708b424001424) (gs:=[(.fork 0x5240001241b052052052406401042000420052420424 []),(.fork 0x47340a47340a00040504640544904243b43b43643647204242042040100005240140f42242240f []),(.fork 0x43b449436407420420 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b21x9 : Block 87 8 (successors 87 8 s21) 90 10 := offMemoRows (code:=0x400400406406406406001406420001) (gs:=[(.fork 0x42040a46f40a42040542440542005640640040640040040640040642042042042042047240142000040140f42040f42042242002a40f []),(.fork 0x47344944904a43843844900040640605205242242247205242247247200042040742040740740640640440447347303204640043b40043b400400407400407400 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b21x10 : Block 87 8 (successors 87 8 s21) 100 10 := offMemoRows (code:=0x40e40e40e40e424472001424400400) (gs:=[(.fork 0x43940604404640500040704242400e421420438044420 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b21x11 : Block 87 8 (successors 87 8 s21) 110 10 := offMemoRows (code:=0x40e40a001472001472421472422472) (gs:=[(.fork 0x43c052406434420052420052472 []),(.fork 0x400012425404406401420052401472 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b21x12 : Block 87 8 (successors 87 8 s21) 120 10 := offMemoRows (code:=0x40e40040040040e40e40e40a40e40e) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b21x13 : Block 87 8 (successors 87 8 s21) 130 10 := offMemoRows (code:=0x40e40e40e40e40e40e40e40e400400) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b21x14 : Block 87 8 (successors 87 8 s21) 140 10 := offMemoRows (code:=0x142100142140e40e40e40e) (gs:=[(.fork 0x4a47240909240640f000403420044420421 []),(.fork 0x425421400012420401000401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc21 : Excluded 87 9 s21 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=10) (q:=15) (by decide) (by decide +kernel)
  intro j;fin_cases j
  · exact b21x0
  · exact b21x1
  · exact b21x2
  · exact b21x3
  · exact b21x4
  · exact b21x5
  · exact b21x6
  · exact b21x7
  · exact b21x8
  · exact b21x9
  · exact b21x10
  · exact b21x11
  · exact b21x12
  · exact b21x13
  · exact b21x14

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc22 : Excluded 87 9 s22 := offAudit (g:=(.saved 6)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc23 : Excluded 87 9 s23 := offAudit (g:=(.saved 0)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc24 : Excluded 87 9 s24 := offAudit (g:=(.saved 6)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b25x0 : Block 87 8 (successors 87 8 s25) 0 10 := offMemoRows (code:=0x42340f424400423001424001423400) (gs:=[(.fork 0x42440a42f40a42440704440742042041541542342340142404640140f42402440f []),(.fork 0x42f42442340a42f40a42340705340742342340640040640042342340540040540042401640142300a40140f42344640f424423 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b25x1 : Block 87 8 (successors 87 8 s25) 10 10 := offMemoRows (code:=0x100142340144640f423001446001) (gs:=[(.fork 0x44640a02440a44640745040744640002640041e41e414414423423401446046401 []),(.fork 0x42340a03340a45044642340745040742342340640f40640f42342340540640540644601640142300a401400423424400446423 []),(.fork 0x40f04440f00040a02440a00040708440700040004440042542505245a000423423 []),(.fork 0x42545a052423423401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b25x2 : Block 87 8 (successors 87 8 s25) 20 10 := offMemoRows (code:=0x406406406406405406001401423001) (gs:=[(.fork 0x42340700040742342342342340540640540640f42344640f40a42300040a400423424400405406406405052423 []),(.fork 0x44600a42400a00a42544a052423401052 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b25x3 : Block 87 8 (successors 87 8 s25) 30 10 := offMemoRows (code:=0x406406406001406406405406406406) (gs:=[(.fork 0x42442f42f42442404442404a406406424424420405420405405404424400423400423400400405400405400424001406406424024 [(.fork 0x42f412022400423 [])])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b25x4 : Block 87 8 (successors 87 8 s25) 40 10 := offMemoRows (code:=0x406406406001406406406406406406) (gs:=[(.fork 0x44602444645045044644602644604a40640644644641e40541e40540540344640f42340f42340f40f40540f40540f446001406406 [(.fork 0x45041302240f423 [])])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b25x5 : Block 87 8 (successors 87 8 s25) 50 10 := offMemoRows (code:=0x424405406406406406406406406406) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b25x6 : Block 87 8 (successors 87 8 s25) 60 10 := offMemoRows (code:=0x1001001405446405446405424405) (gs:=[(.fork 0x4400002200008200004445a04445a04440540545a45a05240645a406406401423401423401401406401406406405405 []),(.fork 0x40540505240642340140140645a406405405 []),(.fork 0x423000423000423446423424405405401401405405405405406406423405052405 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b25x7 : Block 87 8 (successors 87 8 s25) 70 10 := offMemoRows (code:=0x1424001424446424001424001405) (gs:=[(.fork 0x446012424012405406052423401401406052406405052 []),(.fork 0x41c406026402423026423424 []),(.fork 0xc431046428001013400404423044423424 [(.fork 0x42f022412423400 [])]),(.fork 0x405012425401423000401424 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b25x8 : Block 87 8 (successors 87 8 s25) 80 10 := offMemoRows (code:=0x406406423001474407001001423407) (gs:=[(.fork 0x40a02440a00008243b43b46345046304a43843843843842342340100008640140f45000a00045040f45040f400000046400 []),(.fork 0x43b463438438407423423026446 []),(.fork 0x42340a00040a42300040640740640742344642342442342340540640540642342342342342347440142300040140f42344640f400423424400 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b25x9 : Block 87 8 (successors 87 8 s25) 90 10 := offMemoRows (code:=0x424474001424405474001405406406) (gs:=[(.fork 0x40543840642340740502a446406407463406 []),(.fork 0x464436423044423424 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b25x10 : Block 87 8 (successors 87 8 s25) 100 10 := offMemoRows (code:=0x1474446474450446431474001474) (gs:=[(.fork 0x466474423465026423 []),(.fork 0x43c434423084423474 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b25x11 : Block 87 8 (successors 87 8 s25) 110 10 := offMemoRows (code:=0x42300143140a00100142340a001474) (gs:=[(.fork 0x40501242540142300a401474 []),(.fork 0x40702640700002245145146802a46842f42a42a42a42a42342340100002640140f00002640f40042f00a00042f40042f400 []),(.fork 0x45146842a42a40a423423046424 []),(.fork 0x42340700040742300040640a40640a42344642342442342342342340540640540642342342343140142300040140f42344640f400423424400 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b25x12 : Block 87 8 (successors 87 8 s25) 120 10 := offMemoRows (code:=0x144642443142f424405431001405) (gs:=[(.fork 0x40542a40640a40646840642340a40504a424 []),(.fork 0x469454423024423446 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b25x13 : Block 87 8 (successors 87 8 s25) 130 10 := offMemoRows (code:=0x1446001446001431001431446431) (gs:=[(.fork 0x430457423024423431 []),(.fork 0x40501242540142300a401431 []),(.fork 0xc47404646a00101340f403423044423446 [(.fork 0x45002241342340f [])]),(.fork 0x405012425401423000401446 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc25 : Excluded 87 9 s25 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=10) (q:=14) (by decide) (by decide +kernel)
  intro j;fin_cases j
  · exact b25x0
  · exact b25x1
  · exact b25x2
  · exact b25x3
  · exact b25x4
  · exact b25x5
  · exact b25x6
  · exact b25x7
  · exact b25x8
  · exact b25x9
  · exact b25x10
  · exact b25x11
  · exact b25x12
  · exact b25x13

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc26 : Excluded 87 9 s26 := offAudit (g:=(.saved 6)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b27x0 : Block 87 8 (successors 87 8 s27) 0 10 := offMemoRows (code:=0x400405405405001405400406406406) (gs:=[(.fork 0x41540a42a40a42400041540704440740540540040640040600042442442a40540541542441540042440041502440540540141504640140f41500040f [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b27x1 : Block 87 8 (successors 87 8 s27) 10 10 := offMemoRows (code:=0x40540540f40540540500140540f405) (gs:=[(.fork 0x41440a02440a44643841440743840741404441440000040040540540f40640f406000446446000405405414446414406446406405405401414046401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b27x2 : Block 87 8 (successors 87 8 s27) 20 10 := offMemoRows (code:=0x406405406405401405405405001405) (gs:=[(.fork 0x4400040f04440f00040a02440a45a06200040708440700004400040004440040540540540640540645a02445b45a02a45a45a05245a00040645a45a406405405 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b27x3 : Block 87 8 (successors 87 8 s27) 30 10 := offMemoRows (code:=0x406406406406406406406405406406) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b27x4 : Block 87 8 (successors 87 8 s27) 40 10 := offMemoRows (code:=0x406406406406406406001406406406) (gs:=[(.fork 0x2642a02a42a02a42a00042a42a40640642a0c242442442a42a42a40a40a42a40a40640645b45b42a45100c42a45142a40a40a42a40a [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b27x5 : Block 87 8 (successors 87 8 s27) 50 10 := offMemoRows (code:=0x405405406001406406406406406406) (gs:=[(.fork 0x45b00045b00044a44a45b44a02a44a44a45b44a02a44a00044a00040640644a44a45b44a02a44a44a45b44a000406406 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b27x6 : Block 87 8 (successors 87 8 s27) 60 10 := offMemoRows (code:=0x405405001405405405405405405405) (gs:=[(.fork 0x4240502245a08440508200004245a02440545a45b45a02a45a45a05240645a406406401405405405405425405405405 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b27x7 : Block 87 8 (successors 87 8 s27) 70 10 := offMemoRows (code:=0x23415001415414415001415405405) (gs:=[(.fork 0x41c40f046400026402405000405415 []),(.fork 0x1c42a042428048406401046412400404405044405415 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b27x8 : Block 87 8 (successors 87 8 s27) 80 10 := offMemoRows (code:=0x1406405405405407405001405407) (gs:=[(.fork 0x43840a02440a40508240740640740643840646340600443843843843802443802240540543846340540540143808640140f43844b00043840f44b40f400438046400 []),(.fork 0x43808a43806243843843800040640643806244644643843843840740743840740640645b45b00002443843b02443843b438407407438407 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b27x9 : Block 87 8 (successors 87 8 s27) 90 10 := offMemoRows (code:=0x1415405405405405406406406406) (gs:=[(.fork 0x464436405044405407022415 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b27x10 : Block 87 8 (successors 87 8 s27) 100 10 := offMemoRows (code:=0x41443843841442a43800142a415438) (gs:=[(.fork 0x46640602640a04640702642a405465026405 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b27x11 : Block 87 8 (successors 87 8 s27) 110 10 := offMemoRows (code:=0x40540a40500140540a001438001438) (gs:=[(.fork 0x43c072406434405084405062438 []),(.fork 0x40506242545b40640140500a405407006438 []),(.fork 0x42a04442a40702640740502240a40640a40642a46842a40646840600442a42a02242a42a40540540540540142a02640140f42a02640f40042a45900042a400459400 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b27x12 : Block 87 8 (successors 87 8 s27) 120 10 := offMemoRows (code:=0x41542a42a415405405405405405405) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b27x13 : Block 87 8 (successors 87 8 s27) 130 10 := offMemoRows (code:=0x141400142a00142a41442a001414) (gs:=[(.fork 0x46945440502440540a022414 []),(.fork 0x4300c202840645740502440542a []),(.fork 0x4050c242545b40640140500a40540a00642a []),(.fork 0x1c43804246a04840640104641340f403405044405414 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b27x14 : Block 87 8 (successors 87 8 s27) 140 10 := offMemoRows (code:=0x23414) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc27 : Excluded 87 9 s27 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=10) (q:=15) (by decide) (by decide +kernel)
  intro j;fin_cases j
  · exact b27x0
  · exact b27x1
  · exact b27x2
  · exact b27x3
  · exact b27x4
  · exact b27x5
  · exact b27x6
  · exact b27x7
  · exact b27x8
  · exact b27x9
  · exact b27x10
  · exact b27x11
  · exact b27x12
  · exact b27x13
  · exact b27x14

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc40 : Excluded 87 9 s40 := offAudit (g:=(.saved 0)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b41x0 : Block 87 8 (successors 87 8 s41) 0 10 := offMemoRows (code:=0x43640140d40f40d40d40d40d40d40f) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b41x1 : Block 87 8 (successors 87 8 s41) 10 10 := offMemoRows (code:=0x400400400400001401436001001001) (gs:=[(.fork 0x40840f40840f04243300040a43343340a40a000406052406000405022405435408434434429433404404436436 []),(.fork 0x8440e434435404436436401 []),(.fork 0x43641043643643648143643640040740040740f43641040f40a43648140a40643600040640543605240540040740740004a436 []),(.fork 0x43404a43640104204a [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b41x2 : Block 87 8 (successors 87 8 s41) 20 10 := offMemoRows (code:=0x407001407400400400407400400400) (gs:=[(.fork 0x44744744744700004243904240d40d40740744544540d40d02302240d40d43640543640540540740704240d400438400438400400405400405400 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b41x3 : Block 87 8 (successors 87 8 s41) 30 10 := offMemoRows (code:=0x40740e407407407407407407407407) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b41x4 : Block 87 8 (successors 87 8 s41) 40 10 := offMemoRows (code:=0x407407407407407407407407407407) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b41x5 : Block 87 8 (successors 87 8 s41) 50 10 := offMemoRows (code:=0x40040040040040d400400407400407) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b41x6 : Block 87 8 (successors 87 8 s41) 60 10 := offMemoRows (code:=0x1001436405400400400400001400) (gs:=[(.fork 0x40840840e40e40e40e08240e00004241241202302240e40e429042400400404407404407407408408401436401436401401407401407407400400 []),(.fork 0x48240a48240a00040604a40648341643843844848241541543643640100002240140f41602200041640f41640f []),(.fork 0x43848341540543643604640d [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b41x7 : Block 87 8 (successors 87 8 s41) 70 10 := offMemoRows (code:=0x40d40d400400400400436001001405) (gs:=[(.fork 0x41504243640504a046 []),(.fork 0x43640a48140a43640600040643641040740040740043648143643640040740040743643643604640143605240140f43641040f [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b41x8 : Block 87 8 (successors 87 8 s41) 80 10 := offMemoRows (code:=0x100143640600100100108b40d40d) (gs:=[(.fork 0x4a46402241b022000436022436027 []),(.fork 0x41502402740e08a407052436405000405 []),(.fork 0x40d08a024400092434401436000401027 []),(.fork 0x48540a48540a00040504a40548404243b43b47204242042043643640100005240140f42242240f []),(.fork 0x43b484420406436436 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b41x9 : Block 87 8 (successors 87 8 s41) 90 10 := offMemoRows (code:=0x1464400400400400436001464406) (gs:=[(.fork 0x43640a48140a43640500040543600043600043643640040640040643643643646440143600040140f43641040f400407407400 []),(.fork 0x42446443642304a423 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b41x10 : Block 87 8 (successors 87 8 s41) 100 10 := offMemoRows (code:=0x40d40d40d40d40e40e40e40e001464) (gs:=[(.fork 0x41540702246443640504a405 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b41x11 : Block 87 8 (successors 87 8 s41) 110 10 := offMemoRows (code:=0x40e40a40e40e40e40a001464001464) (gs:=[(.fork 0x43c425436052436464 []),(.fork 0x400042434401436052401464 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b41x12 : Block 87 8 (successors 87 8 s41) 120 10 := offMemoRows (code:=0x40e40e40e40e40040040040040e40e) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b41x13 : Block 87 8 (successors 87 8 s41) 130 10 := offMemoRows (code:=0x40d40d40e40e40e40e40e40e40e40e) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b41x14 : Block 87 8 (successors 87 8 s41) 140 10 := offMemoRows (code:=0x40d40d) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc41 : Excluded 87 9 s41 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=10) (q:=15) (by decide) (by decide +kernel)
  intro j;fin_cases j
  · exact b41x0
  · exact b41x1
  · exact b41x2
  · exact b41x3
  · exact b41x4
  · exact b41x5
  · exact b41x6
  · exact b41x7
  · exact b41x8
  · exact b41x9
  · exact b41x10
  · exact b41x11
  · exact b41x12
  · exact b41x13
  · exact b41x14

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc42 : Excluded 87 9 s42 := offAudit (g:=(.saved 7)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc56 : Excluded 87 9 s56 := offAudit (g:=(.saved 7)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc57 : Excluded 87 9 s57 := offAudit (g:=(.saved 13)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc58 : Excluded 87 9 s58 := offAudit (g:=(.saved 7)) certifiedDB (by decide) (by decide +kernel)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem theta_excluded : Excluded 87 10 inputs := by
  apply join_exclusions (by decide +kernel)
  intro v mem
  rw [firstLayer_eq] at mem
  simp only [firstLayer,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact exc0
  · exact exc1
  · exact exc2
  · exact fun h => exc2 (sym3 h)
  · exact exc4
  · exact exc5
  · exact exc6
  · exact exc7
  · exact exc8
  · exact exc9
  · exact exc10
  · exact exc11
  · exact fun h => exc8 (sym12 h)
  · exact fun h => exc9 (sym13 h)
  · exact fun h => exc10 (sym14 h)
  · exact fun h => exc11 (sym15 h)
  · exact exc16
  · exact exc17
  · exact exc18
  · exact fun h => exc18 (sym19 h)
  · exact exc20
  · exact exc21
  · exact exc22
  · exact exc23
  · exact exc24
  · exact exc25
  · exact exc26
  · exact exc27
  · exact fun h => exc20 (sym28 h)
  · exact fun h => exc21 (sym29 h)
  · exact fun h => exc22 (sym30 h)
  · exact fun h => exc23 (sym31 h)
  · exact fun h => exc20 (sym32 h)
  · exact fun h => exc21 (sym33 h)
  · exact fun h => exc22 (sym34 h)
  · exact fun h => exc23 (sym35 h)
  · exact fun h => exc24 (sym36 h)
  · exact fun h => exc25 (sym37 h)
  · exact fun h => exc26 (sym38 h)
  · exact fun h => exc27 (sym39 h)
  · exact exc40
  · exact exc41
  · exact exc42
  · exact fun h => exc42 (sym43 h)
  · exact fun h => exc4 (sym44 h)
  · exact fun h => exc5 (sym45 h)
  · exact fun h => exc6 (sym46 h)
  · exact fun h => exc7 (sym47 h)
  · exact fun h => exc20 (sym48 h)
  · exact fun h => exc21 (sym49 h)
  · exact fun h => exc23 (sym50 h)
  · exact fun h => exc22 (sym51 h)
  · exact fun h => exc0 (sym52 h)
  · exact fun h => exc1 (sym53 h)
  · exact fun h => exc2 (sym54 h)
  · exact fun h => exc2 (sym55 h)
  · exact exc56
  · exact exc57
  · exact exc58
  · exact fun h => exc58 (sym59 h)
  · exact fun h => exc8 (sym60 h)
  · exact fun h => exc9 (sym61 h)
  · exact fun h => exc11 (sym62 h)
  · exact fun h => exc10 (sym63 h)
  · exact fun h => exc56 (sym64 h)
  · exact fun h => exc57 (sym65 h)
  · exact fun h => exc58 (sym66 h)
  · exact fun h => exc58 (sym67 h)
  · exact fun h => exc4 (sym68 h)
  · exact fun h => exc5 (sym69 h)
  · exact fun h => exc6 (sym70 h)
  · exact fun h => exc7 (sym71 h)
  · exact fun h => exc40 (sym72 h)
  · exact fun h => exc41 (sym73 h)
  · exact fun h => exc42 (sym74 h)
  · exact fun h => exc42 (sym75 h)
  · exact fun h => exc8 (sym76 h)
  · exact fun h => exc9 (sym77 h)
  · exact fun h => exc11 (sym78 h)
  · exact fun h => exc10 (sym79 h)
  · exact fun h => exc4 (sym80 h)
  · exact fun h => exc5 (sym81 h)
  · exact fun h => exc6 (sym82 h)
  · exact fun h => exc7 (sym83 h)

end Theta

abbrev B := BitVec 628
abbrev Sig := B × B
def top : B := BitVec.allOnes 628
def zero : Sig := (0,0)
def one : Sig := (top,top)
def target : Sig := (top,0)
def neg (a : Sig) : Sig := (~~~a.1,~~~a.2)
def bin (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1 ||| b.1,a.2 ||| b.2) else (a.1 &&& b.1,a.2 &&& b.2)
def sep (d : Bool) (a : Sig) : B :=
  if d then a.1 ^^^ a.2 else a.1 &&& ~~~a.2
def unionSep (d : Bool) : List Sig → B
  | [] => 0
  | a::l => sep d a ||| unionSep d l

def dropped (del v : List Sig) : List Sig := v.filter (fun x => !(del.contains x))

abbrev Cov := B × B × B

def addCov (z : B) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Sig) : Cov :=
  v.foldr (fun a c => addCov (sep d a) c) (0,0,0)

def takeOne (c : Cov) (a : B) : B := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : B) : B :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

theorem cov_one (c : Cov) (a : B) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

theorem cov_two (c : Cov) (a b : B) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

theorem add_swap (c : Cov) (a b : B) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

theorem cov_perm (d : Bool) {l r : List Sig} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (sep d a)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2

theorem cov_union (d : Bool) (v : List Sig) : (coverage d v).1=unionSep d v := by
  induction v with
  | nil => rfl
  | cons a v ih => change sep d a ||| (coverage d v).1 = (sep d a ||| unionSep d v); rw [ih]

lemma bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

-- Each bit position pairs a positive and a negative input row.
def raw0 : Sig := (0x13000000000000000000007fc0000fffff000003ff800001ffc00000fffffc00000ffff00f811f1c11245f03e70fe01f023e382248be07ce1c88447c3f83c8723f901f40000000000000000000000, 0x1271389c4e271389c4e271389c4e271342684d09a1342684d09a1342684d09a1342684f007800f1c00000f01e707e00f001e3800001e03ce0c00003c3f83c0703f801f00000000000000000000000)
def raw1 : Sig := (0x27007fc01ff007fc0000ff80001ffff80000000000000000000007ff000000007fffff11f88221252f0bc13e217b10889fe821ffffe400840847e2088494bc2f04f885ef807c08f8e08922f81f387, 0x2588c46231188c46231188c46231188c1182304608c1182304608c1182304608c1182200f80000000f03c01e003800001fe001ffffe000000003e00000003c0f007800e7803c0078e00000780f383)
def raw2 : Sig := (0x4c0000000000000001ff00003ffff0000000000000000001fffff800001ffffffff000ff800fffff444104488821fffff11101112451222903c03e047c7044917c0f9c388fc4110929785e09f10bd, 0x48231188c46231188c46231188c462318630c618c318630c618c318630c618c318630cff000fffff000000000001ffffe00000000000000003c01e003c7000003c079c1807c0000000781e00f001c)
def raw3 : Sig := (0x880000001ffff800000000003fe0000000000003fffff00000000000001fffff800000442224424affe00ffff8008844488495ffc01ffff00000000000000000000000011088f87f0790e47f203e8, 0x801c8e472391c8e472391c8e472391c8790f21e43c8790f21e43c8790f21e43c8790f20000000000ffe00ffff8000000000001ffc01ffff00000000000000000000000000000787f0780e07f003e0)
def raw4 : Sig := (0x10007fffe00007fffe00007fc000000000001ffc00000ffe00000000ffe0000000000088444ff410fffff200420423f104424a5e17827c42f7ffffe222022248a24452022111221257ff007fffc00, 0x68341a0d068341a0d068341a0d0680d01a0340680d01a0340680d01a0340680d01a00000ff000fffff000000001f00000001e07803c0073ffffc000000000000000000000000007ff007fffc00)
def raw5 : Sig := (0x20ff8000000000000000ff8000000007ffffe00000000000000007ff0000000000000022111f0fe0f21c8fe407d00000000000000000000003fe003ffffd11041122208442227fa087ffff9002102, 0x170b85c2e170b85c2e170b85c2e1706e0dc1b83706e0dc1b83706e0dc1b83706e0dc00000f0fe0f01c0fe007c00000000000000000000003fc003ffffc00000000000000007f8007ffff8000000)
def raw6 : Sig := (0x40000000000007ffffff0000000000000000000000000ffffffff80000000000000000000000000000000000000044223e1fc1e4391fc80fa221113fd043ffffc8010817fc007ffffa22082244410, 0xd86c361b0d86c361b0d86c361b0d8670ce19c338670ce19c338670ce19c338670ce0000000000000000000000000001e1fc1e0381fc00f8000003fc003ffffc0000007f8007ffff800000000000)
def raw7 : Sig := (0x80fffffffffff8000000000000000007fffffffffffff0000000000000000000000000fffff88880889228911481ff001ffffe888208911041108891092bff803fffe007ffffc4440444914488a40, 0xe070381c0e070381c0e070381c0e0780f01e03c0780f01e03c0780f01e03c0780f00fffff00000000000000001fe001ffffe0000000000000000000003ff803fffe007ffff80000000000000000)

def raw : List Sig := [raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7]

def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one

-- A set records the distinct signals needed by the remaining gates.
-- Read backwards, a gate replaces its output with the operand or operands.
inductive Live : Nat → Nat → Finset Sig → Prop
  | stop : Live 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)) :
      Live (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)) :
      Live (k+1) t (insert a (insert b U))

set_option maxRecDepth 4096 in
lemma target_proper : proper target := by unfold proper target zero one top; decide
lemma live_proper {k t S} (h : Live k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop => simpa using target_proper
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

lemma live_size {k t S} (h : Live k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h with
  | stop => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩

lemma sep_unary (t : Nat) (a : Sig) (i : Nat)
    (h : (sep (decide (0<t)) (neg a)).getLsbD i = true) :
    (sep true a).getLsbD i = true := by
  by_cases hi : i < 628
  · cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases ht : decide (0<t) <;>
      simp only [sep,neg,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 628 ≤ i)] at h

lemma sep_binary (t d : Bool) (a b : Sig) (i : Nat)
    (h : (sep t (bin d a b)).getLsbD i = true) :
    (sep t a).getLsbD i = true ∨ (sep t b).getLsbD i = true := by
  by_cases hi : i < 628
  · cases t <;> cases d <;>
      cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases hu : b.1.getLsbD i <;> cases hv : b.2.getLsbD i <;>
      simp only [sep,bin,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,hu,hv] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 628 ≤ i)] at h

lemma sep_weaken (t : Nat) (a : Sig) (i : Nat) (hi : i < 628)
    (h : (sep (decide (0<t)) a).getLsbD i = true) : (sep true a).getLsbD i = true := by
  cases ht : decide (0<t) <;> cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
    simp only [sep,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h

lemma live_sep {k t S} (h : Live k t S) (i : Nat) (hi : i < 628) :
    ∃ a ∈ S, (sep (decide (0<t)) a).getLsbD i = true := by
  induction h with
  | stop =>
    refine ⟨target,by simp,?_⟩
    change (BitVec.allOnes 628 &&& ~~~(0 : B)).getLsbD i = true
    rw [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_allOnes (v := 628)] <;> simp [hi]
  | unary ha hf _ ih =>
    obtain ⟨x,hx,h⟩ := ih
    simp only [Finset.mem_insert] at hx
    simp only [Nat.zero_lt_succ,decide_true]
    rcases hx with rfl | hU
    · exact ⟨_,Finset.mem_insert_self _ _,sep_unary _ _ _ h⟩
    · exact ⟨x,Finset.mem_insert_of_mem hU,sep_weaken _ _ _ hi h⟩
  | binary ha hb hab hf _ ih =>
    obtain ⟨x,hx,h⟩ := ih
    rcases Finset.mem_insert.mp hx with rfl | hU
    · rcases sep_binary _ _ _ _ _ h with h | h
      · exact ⟨_,Finset.mem_insert_self _ _,h⟩
      · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),h⟩
    · exact ⟨x,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU),h⟩
lemma mem_unionSep (d : Bool) (v : List Sig) (i : Nat) :
    (unionSep d v).getLsbD i = true ↔ ∃ a ∈ v, (sep d a).getLsbD i = true := by
  induction v with
  | nil => simp [unionSep]
  | cons a v ih => simp only [unionSep,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp] <;> aesop

lemma live_cover {k t S} {v : List Sig} (h : Live k t S) (he : v.toFinset=S) :
    unionSep (decide (0<t)) v = top := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain ⟨a,hm,ha⟩ := live_sep h i hi
  have hmem : a ∈ v := List.mem_toFinset.mp (he.symm ▸ hm)
  simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using (mem_unionSep _ _ _).2 ⟨a,hmem,ha⟩

lemma union_append (d : Bool) (l r : List Sig) :
    unionSep d (l++r) = unionSep d l ||| unionSep d r := by
  induction l with
  | nil => simp [unionSep]
  | cons a l ih => simp [unionSep,ih,BitVec.or_assoc]

def keepOf (U : Finset Sig) (del : List Sig) : List Sig := del.filter (fun a => decide (a ∈ U))

lemma edit_list {v del : List Sig} {U : Finset Sig}
    (hv : v.Nodup) (hd : del.Nodup) (he : v.toFinset = del.toFinset ∪ U) :
    (keepOf U del ++ dropped del v).Nodup ∧ (keepOf U del ++ dropped del v).toFinset = U := by
  have memv (x : Sig) : x ∈ v ↔ x ∈ del ∨ x ∈ U := by
    change x ∈ v ↔ _
    rw [← List.mem_toFinset,he]
    simp
  constructor
  · rw [List.nodup_append]
    refine ⟨hd.filter _,hv.filter _,?_⟩
    intro a ha b hb eq
    subst b
    simp [keepOf] at ha
    simp [dropped] at hb
    exact hb.2 ha.1
  · ext x
    simp only [List.mem_toFinset,List.mem_append,List.mem_filter,keepOf,dropped,decide_eq_true_eq,
      Bool.not_eq_true',List.contains_eq_mem,memv]
    by_cases h : x ∈ del <;> simp_all

lemma recover_perm (del v : List Sig) (hv : v.Nodup) (hd : del.Nodup)
    (hs : ∀ x ∈ del, x ∈ v) : v.Perm (del ++ dropped del v) := by
  apply List.perm_of_nodup_nodup_toFinset_eq hv
  · rw [List.nodup_append]
    refine ⟨hd,hv.filter _,?_⟩
    intro a ha b hb e
    subst b
    simp [dropped] at hb
    exact hb.2 ha
  · ext x
    simp only [List.mem_toFinset,List.mem_append,dropped,List.mem_filter,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not]
    by_cases h : x ∈ del <;> simp_all

lemma one_rest (d : Bool) {v : List Sig} {a : Sig} (hv : v.Nodup) (ha : a ∈ v) :
    v.length-1=(dropped [a] v).length ∧
      takeOne (coverage d v) (sep d a)=unionSep d (dropped [a] v) := by
  have p := recover_perm [a] v hv (by simp) (by simpa using ha)
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d p]
    exact (cov_one _ _).trans (cov_union _ _)

lemma two_rest (d : Bool) {v : List Sig} {a b : Sig} (hv : v.Nodup)
    (ha : a ∈ v) (hb : b ∈ v) (hab : a ≠ b) :
    v.length-2=(dropped [a,b] v).length ∧
      takeTwo (coverage d v) (sep d a) (sep d b)=unionSep d (dropped [a,b] v) := by
  have p := recover_perm [a,b] v hv (by simp [hab]) (by simp [ha,hb])
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d p]
    exact (cov_two _ _ _).trans (cov_union _ _)

open PEqualNP.CircuitLowerBounds

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  obtain ⟨p,n⟩ := a
  simp only [bin,one,zero,top,reduceCtorEq,ite_true,ite_false,BitVec.and_allOnes,BitVec.or_allOnes,BitVec.and_zero,BitVec.or_zero,BitVec.and_self,BitVec.or_self,Prod.mk.injEq,and_self] <;> simp

lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one,top]

lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,Live.stop,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩

def bit (side : Bool) (i : Fin 628) (a : Sig) : Bool :=
  (if side then a.1 else a.2).getLsbD i.val

lemma bit_zero (s i) : bit s i zero = false := by cases s <;> simp [bit,zero]
lemma bit_one (s i) : bit s i one = true := by
  cases s <;> change (BitVec.allOnes 628).getLsbD i.val = true <;> rw [BitVec.getLsbD_allOnes] <;> simp
lemma bit_neg (s i) (a : Sig) : bit s i (neg a) = !(bit s i a) := by
  cases s <;> simp only [bit,neg,reduceCtorEq,ite_true,ite_false,BitVec.getLsbD_not,i.isLt,decide_true,Bool.true_and]
lemma bit_bin (s i d) (a b : Sig) : bit s i (bin d a b) =
    (if d then bit s i a || bit s i b else bit s i a && bit s i b) := by
  cases s <;> cases d <;> simp only [bit,bin,reduceCtorEq,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]

lemma b_read (s i) (w : List Sig) (j : Nat) :
    (w.map (bit s i)).getD j false = bit s i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _ _).symm
  | some a => rfl

lemma run_bit (s i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit s i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit s i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _ _
    | cons a l ih =>
      change bit s i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _ _
    | cons a l ih =>
      change bit s i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit s i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _ _

lemma execute_bits (gs : List Gate) (s i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit s i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit s i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit s i g w (hg g (by simp))]

def sample (s : Bool) (i : Fin 628) (j : Fin 8) := bit s i (raw.getD j.val zero)
def edgeF (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma sample_ok : ∀ (s : Bool) (i : Fin 628), edgeF (sample s i) = s := by decide +kernel
lemma raw_id : List.ofFn (fun j : Fin 8 => raw.getD j.val zero) = raw := by rfl
lemma sample_list (s i) : List.ofFn (sample s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 8 => raw.getD j.val zero)).map (bit s i) := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]

def special : List Sig := [raw0,raw3,raw5,raw6]

inductive Restricted : Nat → Nat → Finset Sig → Prop
  | stop : Restricted 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hf : neg a ∉ insert a U) (hr : a ∉ special)
      (tail : Restricted k t (insert (neg a) U)) :
      Restricted (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hf : bin d a b ∉ insert a (insert b U))
      (hra : a ∈ special → d = true ∧ a ∉ U)
      (hrb : b ∈ special → d = true ∧ b ∉ U)
      (tail : Restricted k t (insert (bin d a b) U)) :
      Restricted (k+1) t (insert a (insert b U))

lemma Restricted.live {k t S} (h : Restricted k t S) : Live k t S := by
  induction h with
  | stop => exact Live.stop
  | unary ha hf _ _ ih => exact Live.unary ha hf ih
  | binary ha hb hab hf _ _ _ ih => exact Live.binary ha hb hab hf ih

def gateAvailable (v : List Sig) (g : Sig) : Bool :=
  !(v.contains g) && g != zero && g != one

def tryGate (k t : Nat) (r : List Sig → Bool) (v rest : List Sig) (n : Nat) (c : B) (g : Sig)
    (keep : List (List Sig)) : Bool :=
  let d := decide (0<t)
  let base := sep d g ||| c
  if n = k-t then
    base == top && gateAvailable v g && r (g::rest)
  else keep.any (fun h => decide (n+h.length+1 ≤ k-t+1) &&
    (base ||| unionSep d h == top) && gateAvailable v g && r (g::(h++rest)))

def unaryAt (k t : Nat) (r : List Sig → Bool) (v : List Sig) (c : Cov) (a : Sig) : Bool :=
  !(special.contains a) &&
    tryGate k t r v (dropped [a] v) (v.length-1) (takeOne c (sep (decide (0<t)) a)) (neg a) [[],[a]]

def unaryMoves (k t : Nat) (r : List Sig → Bool) (v : List Sig) : Bool :=
  let c := coverage (decide (0<t)) v
  v.any (unaryAt k t r v c)

def allowedKeeps (a b : Sig) : List (List Sig) :=
  [[],[a],[b],[a,b]].filter (fun w => w.all fun x => !(special.contains x))

def fastBinary (r : List Sig → Bool) (v : List Sig) (a b : Sig) (ua ub : B) : Bool :=
  let rest := dropped [a,b] v
  let use := fun (g : Sig) => gateAvailable v g && r (g::rest)
  ((ua &&& ~~~b.1) == 0 && (ub &&& ~~~a.1) == 0 &&
    !(special.contains a) && !(special.contains b) && use (bin false a b)) ||
    ((ua &&& b.2) == 0 && (ub &&& a.2) == 0 && use (bin true a b))

def slowBinary (k t : Nat) (r : List Sig → Bool) (v : List Sig) (c : Cov) (a b : Sig) : Bool :=
  let rest := dropped [a,b] v
  let mask := takeTwo c (sep (decide (0<t)) a) (sep (decide (0<t)) b)
  ((!(special.contains a) && !(special.contains b)) &&
    tryGate k t r v rest (v.length-2) mask (bin false a b) [[],[a],[b],[a,b]]) ||
    tryGate k t r v rest (v.length-2) mask (bin true a b) (allowedKeeps a b)

def scanPairs {α : Type} (p : α → α → Bool) : List α → Bool
  | [] => false
  | a :: t => t.any (p a) || scanPairs p t

lemma scanPairs_complete {α : Type} (p : α → α → Bool) {a b : α} {v : List α}
    (ha : a ∈ v) (hb : b ∈ v) (hne : a ≠ b)
    (hab : p a b = true) (hba : p b a = true) : scanPairs p v = true := by
  induction v with
  | nil => simp at ha
  | cons h v ih =>
    simp only [scanPairs, Bool.or_eq_true]
    by_cases eqA : a = h
    · subst h
      exact Or.inl (List.any_eq_true.mpr ⟨b, (List.mem_cons.mp hb).resolve_left (Ne.symm hne), hab⟩)
    · have ha' := (List.mem_cons.mp ha).resolve_left eqA
      by_cases eqB : b = h
      · subst h
        exact Or.inl (List.any_eq_true.mpr ⟨a, ha', hba⟩)
      · exact Or.inr (ih ha' ((List.mem_cons.mp hb).resolve_left eqB))

def binaryMoves (k t : Nat) (r : List Sig → Bool) (v : List Sig) : Bool :=
  let d := decide (0<t)
  let c := coverage d v
  if t == 0 && v.length == k+2 then
    let acts := v.map (fun a => (a, c.2.1 &&& sep false a))
    scanPairs (fun a b => fastBinary r v a.1 b.1 a.2 b.2) acts
  else scanPairs (slowBinary k t r v c) v

def stepTest (k t : Nat) (v : List Sig) (u b : List Sig → Bool) : Bool :=
  if t>k+1 ∨ v.length>k+1-t+1 then false else
    v == [target] || (decide (0<t) && unaryMoves k (t-1) u v) || binaryMoves k t b v

lemma gate_found {k t m : Nat} {v rest h : List Sig} {g : Sig} {opts : List (List Sig)}
    {S : Finset Sig} {r : List Sig → Bool} (l : Live m t S)
    (hle : m ≤ k) (hp : proper g) (ha : g ∉ v) (hh : h ∈ opts)
    (hn : (g::(h++rest)).Nodup) (he : (g::(h++rest)).toFinset=S)
    (hr : r (g::(h++rest)) = true) : tryGate k t r v rest rest.length (unionSep (decide (0<t)) rest) g opts = true := by
  obtain ⟨ht,hc⟩ := live_size l
  rw [←he,List.toFinset_card_of_nodup hn] at hc
  simp only [List.length_cons,List.length_append] at hc
  have hl : rest.length+h.length+1 ≤ k-t+1 := by omega
  have cv := live_cover l he
  rw [unionSep,union_append] at cv
  have cov : (sep (decide (0<t)) g ||| unionSep (decide (0<t)) rest) ||| unionSep (decide (0<t)) h = top := by
    rw [← cv]; ac_rfl
  by_cases tight : rest.length=k-t
  · have hz : h.length=0 := by omega
    have hem : h=[] := List.length_eq_zero_iff.mp hz
    subst h
    have ok : sep (decide (0<t)) g ||| unionSep (decide (0<t)) rest = top := by
      simpa [unionSep] using cov
    simp [tryGate,tight,ok,gateAvailable,ha,hp.1,hp.2,hr] at *
  · have hav : gateAvailable v g = true := by simp [gateAvailable, ha, hp.1, hp.2]
    simp only [tryGate, ite_eq_right tight, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq, hav, and_true]
    exact ⟨h,hh,⟨hl,cov⟩,hr⟩

lemma unique_needed (c : Cov) (a b : Sig) (op : Bool)
    (h : sep false (bin op a b) ||| takeTwo c (sep false a) (sep false b)=top) :
    ((c.2.1 &&& sep false a) &&& (if op then b.2 else ~~~b.1)) |||
    ((c.2.1 &&& sep false b) &&& (if op then a.2 else ~~~a.1))=0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hh := congrArg (fun z : B => z.getLsbD i) h
  clear h
  cases op <;> simp only [sep,bin,ite_false,ite_true,takeTwo,top,BitVec.getLsbD_allOnes,
    BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,BitVec.getLsbD_zero,
    reduceCtorEq,hi,decide_true,Bool.true_and] at hh ⊢ <;>
    cases ax : a.1.getLsbD i <;> cases ay : a.2.getLsbD i <;>
    cases bx : b.1.getLsbD i <;> cases byy : b.2.getLsbD i <;>
    cases um : c.2.1.getLsbD i <;> simp [ax,ay,bx,byy,um] at hh ⊢

lemma fast_ok {k r v c a b}
    (hlen : v.length-2=k) (h : slowBinary k 0 r v c a b = true) :
    fastBinary r v a b (c.2.1 &&& sep false a) (c.2.1 &&& sep false b) = true := by
  simp only [slowBinary,tryGate,Nat.sub_zero,hlen,ite_true,decide_false,Bool.or_eq_true,
    Bool.and_eq_true,beq_iff_eq] at h
  simp only [fastBinary, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  rcases h with ⟨⟨ha,hb⟩,⟨hc,hav⟩,hr⟩ | ⟨⟨hc,hav⟩,hr⟩
  · obtain ⟨h1,h2⟩ := BitVec.or_eq_zero_iff.mp (unique_needed c a b false hc)
    exact Or.inl ⟨⟨⟨⟨h1,h2⟩,ha⟩,hb⟩,hav,hr⟩
  · obtain ⟨h1,h2⟩ := BitVec.or_eq_zero_iff.mp (unique_needed c a b true hc)
    exact Or.inr ⟨⟨h1,h2⟩,hav,hr⟩

lemma unary_found {m t k : Nat} {U : Finset Sig} {a : Sig} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a U) (hle : m ≤ k)
    (fresh : neg a ∉ insert a U) (ha : a ∉ special) (l : Restricted m t (insert (neg a) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (neg a) U → r v = true) :
    unaryMoves k t r v = true := by
  let h := keepOf U [a]
  let rest := dropped [a] v
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  obtain ⟨hn,eq⟩ := edit_list (del := [a]) (U := U) hv (by simp) (by simpa using he)
  change (h++rest).Nodup at hn
  change (h++rest).toFinset=U at eq
  have nn : neg a ∉ v := fun hm => fresh (he ▸ List.mem_toFinset.mpr hm)
  have nz : neg a ∉ U := fun hm => fresh (Finset.mem_insert_of_mem hm)
  have hnd : (neg a::(h++rest)).Nodup := List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm),hn⟩
  have e : (neg a::(h++rest)).toFinset=insert (neg a) U := by rw [List.toFinset_cons,eq]
  have opts : h ∈ [[],[a]] := by by_cases hm : a ∈ U <;> simp [h,keepOf,hm]
  apply List.any_eq_true.mpr
  refine ⟨a,ah,?_⟩
  unfold unaryAt
  obtain ⟨hlen,hmask⟩ := one_rest (decide (0<t)) hv ah
  rw [hlen,hmask]
  apply Bool.and_eq_true_iff.mpr
  exact ⟨by simp [ha], gate_found l.live hle (live_proper l.live _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)⟩

lemma slow_found {m t k : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a (insert b U)) (hle : m ≤ k)
    (hab : a≠b) (fresh : bin d a b ∉ insert a (insert b U))
    (hra : a ∈ special → d = true ∧ a ∉ U)
    (hrb : b ∈ special → d = true ∧ b ∉ U)
    (l : Restricted m t (insert (bin d a b) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (bin d a b) U → r v = true) :
    slowBinary k t r v (coverage (decide (0<t)) v) a b = true := by
  let g := bin d a b
  let h := keepOf U [a,b]
  let rest := dropped [a,b] v
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have bh : b ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  obtain ⟨hn,eq⟩ := edit_list (del := [a,b]) (U := U) hv (by simp [hab]) (by simpa using he)
  change (h++rest).Nodup at hn
  change (h++rest).toFinset=U at eq
  have nn : g ∉ v := fun hm => fresh (he ▸ List.mem_toFinset.mpr hm)
  have nz : g ∉ U := fun hm => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
  have hnd : (g::(h++rest)).Nodup := List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm),hn⟩
  have e : (g::(h++rest)).toFinset=insert g U := by rw [List.toFinset_cons,eq]
  have opts : h ∈ [[],[a],[b],[a,b]] := by
    by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;> simp [h,keepOf,ha,hb]
  have allow : h ∈ allowedKeeps a b := by
    apply List.mem_filter.mpr
    refine ⟨opts,List.all_eq_true.mpr (fun x hx => ?_)⟩
    have hm : x ∈ U := (List.mem_filter.mp hx).2 |> of_decide_eq_true
    rcases List.mem_cons.mp (List.mem_filter.mp hx).1 with rfl | hx
    · simpa using fun ha : x ∈ special => (hra ha).2 hm
    · obtain rfl := List.mem_singleton.mp hx
      simpa using fun hb : x ∈ special => (hrb hb).2 hm
  obtain ⟨hlen,hmask⟩ := two_rest (decide (0<t)) hv ah bh hab
  unfold slowBinary
  dsimp only
  rw [hlen,hmask]
  cases d with
  | false =>
    have na : a ∉ special := fun ha => Bool.false_ne_true (hra ha).1
    have nb : b ∉ special := fun hb => Bool.false_ne_true (hrb hb).1
    apply Bool.or_eq_true_iff.mpr
    left
    exact Bool.and_eq_true_iff.mpr ⟨by simp [na,nb],
      gate_found l.live hle (live_proper l.live _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)⟩
  | true =>
    apply Bool.or_eq_true_iff.mpr
    right
    exact gate_found l.live hle (live_proper l.live _ (Finset.mem_insert_self _ _)) nn allow hnd e (ih _ hnd e)

lemma binary_found {m t k : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a (insert b U)) (hle : m ≤ k)
    (hab : a≠b) (fresh : bin d a b ∉ insert a (insert b U))
    (hra : a ∈ special → d = true ∧ a ∉ U)
    (hrb : b ∈ special → d = true ∧ b ∉ U)
    (l : Restricted m t (insert (bin d a b) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (bin d a b) U → r v = true) :
    binaryMoves k t r v = true := by
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have bh : b ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have h1 := slow_found hv he hle hab fresh hra hrb l ih
  have e' : v.toFinset = insert b (insert a U) := by rwa [Finset.insert_comm b a]
  have hf : bin d b a ∉ insert b (insert a U) := by rwa [bin_comm d b a, Finset.insert_comm b a]
  have ht : Restricted m t (insert (bin d b a) U) := by rwa [bin_comm d b a]
  have h2 := slow_found hv e' hle hab.symm hf hrb hra ht (by simpa only [bin_comm d b a] using ih)
  unfold binaryMoves
  split
  · rename_i cut
    simp only [Bool.and_eq_true, beq_iff_eq] at cut
    obtain ⟨rfl,hvlen⟩ := cut
    have hlen : v.length - 2 = k := by omega
    let f := fun x => (x, (coverage false v).2.1 &&& sep false x)
    have na : f a ∈ v.map f := List.mem_map_of_mem ah
    have nb : f b ∈ v.map f := List.mem_map_of_mem bh
    exact scanPairs_complete _ na nb (fun e => hab (congrArg Prod.fst e))
      (fast_ok hlen h1) (fast_ok hlen h2)
  · exact scanPairs_complete _ ah bh hab h1 h2

lemma reduced_step {m t S : Nat} {s : Finset Sig} {v : List Sig} {u b : List Sig → Bool}
    (h : Restricted m t s) (hb : m ≤ S+1) (hv : v.Nodup) (he : v.toFinset = s)
    (hu : ∀ w, w.Nodup → ∀ l ≤ S, Restricted l (t-1) w.toFinset → u w = true)
    (hb' : ∀ w, w.Nodup → ∀ l ≤ S, Restricted l t w.toFinset → b w = true) :
    stepTest S t v u b = true := by
  have size := live_size h.live
  rw [← he, List.toFinset_card_of_nodup hv] at size
  rw [stepTest, if_neg (by omega)]
  cases h with
  | stop =>
    have p : v.Perm [target] := List.perm_of_nodup_nodup_toFinset_eq hv (by simp) (by simp [he])
    have eq := List.perm_singleton.mp p
    simp [eq]
  | @unary m t U a ha hf hr tail =>
    apply Bool.or_eq_true_iff.mpr
    left
    apply Bool.or_eq_true_iff.mpr
    right
    apply Bool.and_eq_true_iff.mpr
    refine ⟨by simp, unary_found hv he (by omega) hf hr tail ?_⟩
    intro w hn hs
    exact hu w hn m (by omega) (hs.symm ▸ tail)
  | @binary m t U a b d ha hc hab hf hra hrb tail =>
    apply Bool.or_eq_true_iff.mpr
    right
    apply binary_found hv he (by omega) hab hf hra hrb tail
    intro w hn hs
    exact hb' w hn m (by omega) (hs.symm ▸ tail)

def Impossible (k t : Nat) (v : List Sig) : Prop :=
  ∀ m ≤ k, ¬ Restricted m t v.toFinset

lemma exclude_step {k t : Nat} {v : List Sig} {u b : List Sig → Bool} (hv : v.Nodup)
    (hu : ∀ w, u w = false → Impossible k (t-1) w)
    (hb : ∀ w, b w = false → Impossible k t w)
    (hc : stepTest k t v u b = false) : Impossible (k+1) t v := by
  intro m hm h
  have hu' : ∀ w, w.Nodup → ∀ j ≤ k, Restricted j (t-1) w.toFinset → u w = true := by
    intro w _ j hj r
    cases e : u w
    · exact (hu _ e j hj r).elim
    · rfl
  have hb' : ∀ w, w.Nodup → ∀ j ≤ k, Restricted j t w.toFinset → b w = true := by
    intro w _ j hj r
    cases e : b w
    · exact (hb _ e j hj r).elim
    · rfl
  exact Bool.false_ne_true (hc.symm.trans (reduced_step h hm hv rfl hu' hb'))

-- Each projection below fixes one degree-two input to zero.

def marker : Fin 4 → Sig := ![raw0,raw3,raw5,raw6]
def packed (i : Fin 4) (a : Sig) : BitVec 174 :=
  a.2.extractLsb' (87*i.val) 87 ++ a.1.extractLsb' (87*i.val) 87
def refBit (a : Sig) := a.2.getLsbD 348
def imageWire (i : Fin 4) (a : Sig) : Theta.Wire :=
  (refBit a, (if refBit a then ~~~(packed i a) else packed i a).toNat)
def column (i : Fin 4) (a : Sig) := (imageWire i a).2

lemma packed_neg (i : Fin 4) (a : Sig) : packed i (neg a) = ~~~(packed i a) := by
  have h : 87 * i.val + 87 < 628 := by have := i.isLt; omega
  simp only [packed, neg, BitVec.extractLsb'_not_of_lt h]
  exact BitVec.not_append.symm

lemma packed_bin (i : Fin 4) (d : Bool) (a b : Sig) :
    packed i (bin d a b) = if d then packed i a ||| packed i b else packed i a &&& packed i b := by
  cases d <;> simp [packed,bin,BitVec.extractLsb'_and,BitVec.extractLsb'_or]
  · exact BitVec.and_append.symm
  · exact BitVec.or_append.symm

lemma image_neg (i : Fin 4) (a : Sig) : imageWire i (neg a) = Theta.flip (imageWire i a) := by
  have h : refBit (neg a) = !(refBit a) := by simp [refBit, neg, BitVec.getLsbD_not]
  simp only [imageWire, h, packed_neg, Theta.flip]
  cases refBit a <;> simp

lemma normalize_and (p q : Bool) (a b : BitVec 174) :
    ((p && q), (if p && q then ~~~(a &&& b) else a &&& b).toNat) =
      Theta.meet (p,(if p then ~~~a else a).toNat) (q,(if q then ~~~b else b).toNat) := by
  cases p <;> cases q <;> simp only [Bool.false_and, Bool.true_and, Bool.false_eq_true,
    ite_false, ite_true, Theta.meet, Theta.opIndex, Theta.combine, ← BitVec.toNat_and,
    ← BitVec.toNat_or, ← BitVec.toNat_xor]
  all_goals first | rfl | (congr 2 <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj <;>
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, BitVec.getLsbD_xor,
        hj, decide_true, Bool.true_and] <;>
      cases (a.getLsbD j) <;> cases (b.getLsbD j) <;> rfl)

lemma image_and (i : Fin 4) (a b : Sig) :
    imageWire i (bin false a b) = Theta.meet (imageWire i a) (imageWire i b) := by
  have h : refBit (bin false a b) = (refBit a && refBit b) := by simp [refBit,bin]
  simpa only [imageWire,h,packed_bin,Bool.false_eq_true,ite_false] using normalize_and (refBit a) (refBit b) (packed i a) (packed i b)

lemma image_or (i : Fin 4) (a b : Sig) :
    imageWire i (bin true a b) = Theta.join (imageWire i a) (imageWire i b) := by
  have eq : bin true a b = neg (bin false (neg a) (neg b)) := by
    apply Prod.ext <;> simp [bin,neg,BitVec.not_and]
  rw [eq,image_neg,image_and,image_neg,image_neg]
  rfl

lemma column_bin (i : Fin 4) (d : Bool) (a b : Sig) :
    ∃ tag < 4, column i (bin d a b) = Theta.combine tag (column i a) (column i b) := by
  cases d
  · exact ⟨_,Theta.op_lt _ _,congrArg Prod.snd (image_and i a b)⟩
  · exact ⟨_,Theta.op_lt _ _,congrArg Prod.snd (image_or i a b)⟩

def Feasible (i : Fin 4) (k : Nat) (S : Finset Sig) : Prop :=
  ∃ m ≤ k, ∃ T, Theta.Live 87 m T ∧ ∀ z ∈ T, ∃ a ∈ S, column i a = z

lemma feasible_mono {i : Fin 4} {k k' : Nat} {S : Finset Sig}
    (h : Feasible i k S) (hk : k ≤ k') : Feasible i k' S := by
  obtain ⟨m,hm,T,hl,hs⟩ := h
  exact ⟨m,hm.trans hk,T,hl,hs⟩

lemma feasible_free {i : Fin 4} {k : Nat} {S S' : Finset Sig} {g : Sig}
    (hs : S' ⊆ insert g S) (hr : column i g = 0 ∨ ∃ a ∈ S, column i a = column i g)
    (h : Feasible i k S') : Feasible i k S := by
  obtain ⟨m,hm,T,hl,small⟩ := h
  refine ⟨m,hm,T,hl,fun z hz => ?_⟩
  obtain ⟨b,hb,rfl⟩ := small z hz
  rcases Finset.mem_insert.mp (hs hb) with rfl | hb
  · exact hr.resolve_left (Theta.liveNonzero hl _ hz)
  · exact ⟨b,hb,rfl⟩

lemma free_unary {i : Fin 4} {k : Nat} {a : Sig} {U : Finset Sig}
    (h : Feasible i k (insert (neg a) U)) : Feasible i k (insert a U) := by
  apply feasible_free (g := neg a) (by simp [Finset.insert_subset_iff]; exact fun _ hx => by simp [hx]) _ h
  exact Or.inr ⟨a,Finset.mem_insert_self _ _,(congrArg Prod.snd (image_neg i a)).symm⟩

lemma pull_unary {i : Fin 4} {k : Nat} {a : Sig} {U : Finset Sig}
    (h : Feasible i k (insert (neg a) U)) : Feasible i (k+1) (insert a U) :=
  feasible_mono (free_unary h) (by omega)

lemma pull_binary_cost {i : Fin 4} {q : Nat} {a b : Sig} {d : Bool} {U : Finset Sig}
    (h : Feasible i q (insert (bin d a b) U)) :
    let S := insert a (insert b U)
    let av := S.toList.map (column i)
    Feasible i (q + (Theta.charge av (column i (bin d a b))).toNat) S := by
  let S := insert a (insert b U)
  let av := S.toList.map (column i)
  obtain ⟨tag,ht,eq⟩ := column_bin i d a b
  have ma : column i a ∈ av := List.mem_map.mpr ⟨a,Finset.mem_toList.mpr (Finset.mem_insert_self _ _),rfl⟩
  have mb : column i b ∈ av := List.mem_map.mpr ⟨b,Finset.mem_toList.mpr (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)),rfl⟩
  obtain ⟨m,hm,T,l,small⟩ := h
  have next : Theta.Possible 87 q (av ++ [Theta.combine tag (column i a) (column i b)]) := by
    refine ⟨m,T,hm,l,fun v hv => ?_⟩
    obtain ⟨w,hw,rfl⟩ := small v hv
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simp [eq]
    · apply List.mem_append_left
      exact List.mem_map.mpr ⟨w,Finset.mem_toList.mpr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw)),rfl⟩
  obtain ⟨r,R,cap,hl,hs⟩ := Theta.pullPaid ht ma mb next
  refine ⟨r,by simpa only [av,S,eq] using cap,R,hl,fun v hv => ?_⟩
  obtain ⟨w,hw,ev⟩ := List.mem_map.mp (hs v hv)
  exact ⟨w,Finset.mem_toList.mp hw,ev⟩

lemma pull_binary {i : Fin 4} {q : Nat} {a b : Sig} {d : Bool} {U : Finset Sig}
    (h : Feasible i q (insert (bin d a b) U)) : Feasible i (q+1) (insert a (insert b U)) := by
  apply feasible_mono (pull_binary_cost h)
  cases Theta.charge _ _ <;> simp

lemma free_binary_left {i : Fin 4} {q : Nat} {a b : Sig} {d : Bool} {U : Finset Sig}
    (ha : column i a = 0) (h : Feasible i q (insert (bin d a b) U)) :
    Feasible i q (insert a (insert b U)) := by
  apply feasible_free (g := bin d a b) (by simp [Finset.insert_subset_iff]; exact fun _ hx => by simp [hx]) _ h
  obtain ⟨tag,ht,e⟩ := column_bin i d a b
  rcases Theta.combine_eq_cases tag _ _ ht (Or.inl ha) with hh | hh | hh
  · exact Or.inl (e.trans hh)
  · exact Or.inr ⟨a,by simp,(e.trans hh).symm⟩
  · exact Or.inr ⟨b,by simp,(e.trans hh).symm⟩

lemma free_binary_right {i : Fin 4} {q : Nat} {a b : Sig} {d : Bool} {U : Finset Sig}
    (hb : column i b = 0) (h : Feasible i q (insert (bin d a b) U)) :
    Feasible i q (insert a (insert b U)) := by
  rw [bin_comm] at h
  rw [Finset.insert_comm]
  exact free_binary_left hb h

lemma target_good (i : Fin 4) :
    Theta.Good 87 (column i target) ∧ column i target ≠ 0 := by
  have eq : ∀ j : Fin 4, column j target = 2^87-1 := by decide +kernel
  rw [eq]
  constructor
  · intro j hj
    simp only [Nat.testBit_two_pow_sub_one,decide_eq_true hj,decide_eq_false (show ¬ 87+j<87 by omega)]
    decide
  · decide

lemma feasible_live {k t : Nat} {S : Finset Sig} (h : Live k t S) (i : Fin 4) :
    Feasible i (k-t) S := by
  induction h with
  | stop =>
    refine ⟨0,by decide,{column i target},Theta.Live.done (target_good i).1 (target_good i).2,?_⟩
    simp
  | unary _ _ _ ih => simpa only [Nat.add_sub_add_right] using free_unary ih
  | @binary k t U a b d _ _ _ _ tail ih =>
    apply feasible_mono (pull_binary ih)
    have := (live_size tail).1
    omega

lemma feasible_const {k t : Nat} {S : Finset Sig} (h : Live k t S)
    (i : Fin 4) (a : Sig) (ha : a ∈ S) (hc : column i a = 0) :
    ∃ q, q + t < k ∧ Feasible i q S := by
  induction h generalizing a with
  | stop =>
    have eq : a = target := Finset.mem_singleton.mp ha
    exact ((target_good i).2 (eq ▸ hc)).elim
  | @unary k t U b hp hf tail ih =>
    rcases Finset.mem_insert.mp ha with rfl | ha
    · have hz : column i (neg a) = 0 := (congrArg Prod.snd (image_neg i a)).trans hc
      obtain ⟨q,hq,hf⟩ := ih _ (Finset.mem_insert_self _ _) hz
      exact ⟨q,by omega,free_unary hf⟩
    · obtain ⟨q,hq,hf⟩ := ih _ (Finset.mem_insert_of_mem ha) hc
      exact ⟨q,by omega,free_unary hf⟩
  | @binary k t U b c d hb hc' hbc hf tail ih =>
    have ht := (live_size tail).1
    rcases Finset.mem_insert.mp ha with rfl | hU
    · exact ⟨k-t,by omega,free_binary_left hc (feasible_live tail i)⟩
    · rcases Finset.mem_insert.mp hU with rfl | hU
      · exact ⟨k-t,by omega,free_binary_right hc (feasible_live tail i)⟩
      · obtain ⟨q,hq,hf⟩ := ih _ (Finset.mem_insert_of_mem hU) hc
        exact ⟨q+1,by omega,pull_binary hf⟩

def input (j : Fin 8) := raw.getD j.val zero
def seed (j : Fin 8) := raw ++ [neg (input j),one,zero]

lemma marker_zero (i : Fin 4) : column i (marker i) = 0 := by
  revert i
  decide +kernel

lemma marker_false_and (i : Fin 4) (a : Sig) : column i (bin false (marker i) a) = 0 := by
  have m : ∀ j : Fin 4, imageWire j (marker j) = Theta.zero := by decide +kernel
  change (imageWire i _).2 = 0
  rw [image_and, m]
  cases hp : imageWire i a with
  | mk b z => cases b <;> simp [Theta.meet,Theta.zero,Theta.opIndex,Theta.combine]

lemma mem_raw_input {a : Sig} (h : a ∈ raw) : ∃ v : Fin 8, input v = a := by
  rw [← raw_id] at h
  simpa only [List.mem_ofFn,input] using h

lemma projected_root (j : Fin 8) (i : Fin 4) (q : Nat) (S : Finset Sig)
    (sub : ∀ a ∈ S, a ∈ seed j) (feasible : Feasible i q S) : 11 ≤ q := by
  have rawTable : ∀ (k : Fin 4) (u : Fin 8),
      column k (input u) = 0 ∨ column k (input u) ∈ Theta.inputs := by decide +kernel
  have zeros : ∀ k : Fin 4, column k zero = 0 ∧ column k one = 0 := by decide +kernel
  have table (v : Sig) (hv : v ∈ seed j) : column i v = 0 ∨ column i v ∈ Theta.inputs := by
    simp only [seed,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with h | rfl | rfl | rfl
    · obtain ⟨u,rfl⟩ := mem_raw_input h
      exact rawTable i u
    · have same : column i (neg (input j)) = column i (input j) := by
        unfold column
        rw [image_neg]
        rfl
      rw [same]
      exact rawTable i j
    · exact Or.inl (zeros i).2
    · exact Or.inl (zeros i).1
  obtain ⟨m,cap,T,h,s⟩ := feasible
  have allInputs (z : Nat) (hmem : z ∈ T) : z ∈ Theta.inputs := by
    obtain ⟨a,ha,rfl⟩ := s z hmem
    exact (table a (sub a ha)).resolve_left (Theta.liveNonzero h _ hmem)
  have same := Theta.initial h allInputs
  by_contra! small
  exact Theta.theta_excluded ⟨m,by omega,same ▸ h,by decide +kernel⟩

lemma witness_needed {k t : Nat} {S : Finset Sig} (live : Live k t S)
    (j : Fin 8) (sub : ∀ a ∈ S, a ∈ seed j)
    (v : Fin 8) (active : v ≠ j ∨ t = 0) : input v ∈ S := by
  let p := 620+v.val
  have hp : p < 628 := by have := v.isLt; dsimp [p]; omega
  obtain ⟨a,ha,sec⟩ := live_sep live p hp
  have rawTest : ∀ (d : Bool) (i u : Fin 8),
      (sep d (input u)).getLsbD (620+i.val) = decide (u=i) := by decide +kernel
  have invTest : ∀ (d : Bool) (i u : Fin 8),
      (sep d (neg (input u))).getLsbD (620+i.val) = (d && decide (u=i)) := by decide +kernel
  have good := live_proper live a ha
  have cases := sub a ha
  simp only [seed,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with h | rfl | rfl | rfl
  · obtain ⟨u,rfl⟩ := mem_raw_input h
    rw [rawTest] at sec
    exact (of_decide_eq_true sec : u = v) ▸ ha
  · rw [invTest] at sec
    obtain ⟨pos,eq⟩ := Bool.and_eq_true_iff.mp sec
    rcases active with ne | z
    · exact (ne (of_decide_eq_true eq).symm).elim
    · simp [z] at pos
  · exact (good.2 rfl).elim
  · exact (good.1 rfl).elim

lemma no_inversions {k t : Nat} {S : Finset Sig} (live : Live k t S) (cap : k ≤ 12)
    (j : Fin 8) (sub : ∀ a ∈ S, a ∈ seed j) : t = 0 := by
  have someMarker : ∃ i : Fin 4, marker i ∈ S := by
    by_cases h : j = 0
    · exact ⟨1,witness_needed live j sub 3 (.inl (by subst j; decide))⟩
    · exact ⟨0,witness_needed live j sub 0 (.inl (Ne.symm h))⟩
  obtain ⟨i,hi⟩ := someMarker
  obtain ⟨q,smaller,has⟩ := feasible_const live i (marker i) hi (marker_zero i)
  have lower := projected_root j i q S sub has
  omega

def ProjectBound (k : Nat) (S : Finset Sig) : Prop :=
  ∀ i q, q + (if marker i ∈ S then 1 else 0) < k → ¬ Feasible i q S

lemma initial_bound {k : Nat} {S : Finset Sig} (live : Live k 0 S) (cap : k ≤ 12)
    (j : Fin 8) (sub : ∀ a ∈ S, a ∈ seed j) : ProjectBound k S := by
  intro i q h feasible
  have mark : marker i ∈ S := by
    have num : ∀ p : Fin 4, marker p = input (![0,3,5,6] p) := by decide +kernel
    rw [num]
    exact witness_needed live j sub _ (.inr rfl)
  rw [if_pos mark] at h
  have := projected_root j i q S sub feasible
  omega

lemma mem_special (a : Sig) : a ∈ special ↔ ∃ i, marker i = a := by
  rw [← List.mem_ofFn]
  rfl

lemma bound_binary {k : Nat} {a b : Sig} {d : Bool} {U : Finset Sig}
    (h : ProjectBound (k+1) (insert a (insert b U))) :
    ProjectBound k (insert (bin d a b) U) := by
  intro i q hq hf
  by_cases hp : marker i ∈ insert a (insert b U)
  · by_cases ht : marker i ∈ insert (bin d a b) U
    · rw [if_pos ht] at hq
      exact h i (q+1) (by simp [hp]; omega) (pull_binary hf)
    · rw [if_neg ht] at hq
      rcases Finset.mem_insert.mp hp with ha | hb
      · exact h i q (by simp [hp]; omega) (free_binary_left (ha ▸ marker_zero i) hf)
      · rcases Finset.mem_insert.mp hb with hb | hU
        · exact h i q (by simp [hp]; omega) (free_binary_right (hb ▸ marker_zero i) hf)
        · exact (ht (Finset.mem_insert_of_mem hU)).elim
  · exact h i (q+1) (by simp [hp]; split at hq <;> omega) (pull_binary hf)

lemma restricted_binary {k t : Nat} {a b : Sig} {d : Bool} {U : Finset Sig}
    (h : ProjectBound (k+1) (insert a (insert b U))) (tail : Live k t (insert (bin d a b) U)) :
    (a ∈ special → d = true ∧ a ∉ U) ∧ (b ∈ special → d = true ∧ b ∉ U) := by
  have leftSide {a b : Sig} (h : ProjectBound (k+1) (insert a (insert b U)))
      (tail : Live k t (insert (bin d a b) U)) (hm : a ∈ special) : d = true ∧ a ∉ U := by
    obtain ⟨i,rfl⟩ := (mem_special _).mp hm
    constructor
    · cases d
      · exfalso
        obtain ⟨q,hq,hf⟩ := feasible_const tail i _ (Finset.mem_insert_self _ _) (marker_false_and i b)
        exact h i q (by simp; omega) (free_binary_left (marker_zero i) hf)
      · rfl
    · intro hU
      obtain ⟨q,hq,hf⟩ := feasible_const tail i _ (Finset.mem_insert_of_mem hU) (marker_zero i)
      exact h i q (by simp; omega) (free_binary_left (marker_zero i) hf)
  refine ⟨leftSide h tail, ?_⟩
  apply leftSide (a := b) (b := a)
  · rwa [Finset.insert_comm]
  · rwa [bin_comm]

lemma restrict_live {k t S} (h : Live k t S) (hn : t = 0) (hb : ProjectBound k S) :
    Restricted k t S := by
  induction h with
  | stop => exact Restricted.stop
  | unary => omega
  | binary ha hg hab hf tail ih =>
    obtain ⟨h1,h2⟩ := restricted_binary hb tail
    exact Restricted.binary ha hg hab hf h1 h2 (ih hn (bound_binary hb))

lemma root_choices {k : Nat} {S : Finset Sig} (live : Live k 0 S)
    (j : Fin 8) (sub : ∀ a ∈ S, a ∈ seed j) :
    S = raw.toFinset ∨ S = (raw ++ [neg (input j)]).toFinset := by
  have allRaw (a : Sig) (ha : a ∈ raw) : a ∈ S := by
    obtain ⟨v,rfl⟩ := mem_raw_input ha
    exact witness_needed live j sub v (.inr rfl)
  have other (a : Sig) (ha : a ∈ S) : a ∈ raw ∨ a = neg (input j) := by
    have hs := sub a ha
    simp only [seed,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hs
    have good := live_proper live a ha
    exact hs.elim Or.inl (fun h => Or.inr (h.resolve_right (fun e => e.elim good.2 good.1)))
  by_cases h : neg (input j) ∈ S
  · right
    ext a
    simp only [List.mem_toFinset,List.mem_append,List.mem_singleton]
    exact ⟨other a,fun ha => ha.elim (allRaw a) (fun e => e ▸ h)⟩
  · left
    ext a
    simp only [List.mem_toFinset]
    exact ⟨fun ha => (other a ha).resolve_right (fun e => h (e ▸ ha)),allRaw a⟩

lemma two_constants {k t : Nat} {S : Finset Sig} (h : Live k t S)
    (i : Fin 4) (x y : Sig) (hx : x ∈ S) (hy : y ∈ S) (ne : x ≠ y)
    (cx : column i x = 0) (cy : column i y = 0) (ht : t = 0) :
    ∃ q, q + 2 ≤ k ∧ Feasible i q S := by
  induction h generalizing x y with
  | stop =>
    exact ((target_good i).2 ((Finset.mem_singleton.mp hx) ▸ cx)).elim
  | unary => omega
  | @binary k t U a b d _ _ _ _ tail ih =>
    have spent (c : column i a = 0 ∨ column i b = 0)
        (z : Sig) (zmem : z ∈ insert (bin d a b) U) (cz : column i z = 0) :
        ∃ q, q + 2 ≤ k+1 ∧ Feasible i q (insert a (insert b U)) := by
      obtain ⟨q,hq,hf⟩ := feasible_const tail i z zmem cz
      exact ⟨q,by omega,c.elim (fun e => free_binary_left e hf) (fun e => free_binary_right e hf)⟩
    have consumed (w : Sig) (hw : w ∈ insert a (insert b U)) (abs : w ∉ U) : w = a ∨ w = b := by
      simpa [abs] using hw
    by_cases xU : x ∈ U
    · by_cases yU : y ∈ U
      · obtain ⟨q,hq,feasible⟩ := ih x y (Finset.mem_insert_of_mem xU) (Finset.mem_insert_of_mem yU) ne cx cy ht
        exact ⟨q+1,by omega,pull_binary feasible⟩
      · have e := consumed y hy yU
        exact spent (e.imp (fun (eq : y = a) => eq ▸ cy) (fun (eq : y = b) => eq ▸ cy)) x (Finset.mem_insert_of_mem xU) cx
    · have e := consumed x hx xU
      by_cases yU : y ∈ U
      · exact spent (e.imp (fun (eq : x = a) => eq ▸ cx) (fun (eq : x = b) => eq ▸ cx)) y (Finset.mem_insert_of_mem yU) cy
      · have f := consumed y hy yU
        have both : column i a = 0 ∧ column i b = 0 := by
          rcases e with rfl | rfl <;> rcases f with rfl | rfl <;> simp_all
        obtain ⟨op,lt,val⟩ := column_bin i d a b
        have cz : column i (bin d a b) = 0 := by
          rcases Theta.combine_eq_cases op _ _ lt (.inl both.1) with eq | eq | eq
          · exact val.trans eq
          · exact val.trans (eq.trans both.1)
          · exact val.trans (eq.trans both.2)
        exact spent (.inl both.1) _ (Finset.mem_insert_self _ _) cz

lemma low_excluded {k : Nat} {S : Finset Sig} (h : Live k 0 S)
    (cap : k ≤ 12) (eq : S = (raw ++ [neg raw0]).toFinset) : False := by
  have left : raw0 ∈ S := eq ▸ (by decide +kernel)
  have right : neg raw0 ∈ S := eq ▸ (by decide +kernel)
  have sub (a : Sig) (ha : a ∈ S) : a ∈ seed 0 := by
    rw [eq,List.mem_toFinset] at ha
    rcases List.mem_append.mp ha with l | r
    · exact List.mem_append_left _ l
    · have e := List.mem_singleton.mp r
      subst a
      exact List.mem_append_right _ (List.mem_cons_self ..)
  obtain ⟨q,hq,hf⟩ := two_constants h 0 raw0 (neg raw0) left right (by decide +kernel)
    (by decide +kernel) (by decide +kernel) rfl
  have := projected_root 0 0 q S sub hf
  omega

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def perm : Fin 8 → Fin 8 → Fin 8 :=
  ![![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![3,2,1,0,7,6,5,4],![3,2,1,0,7,6,5,4],
    ![0,4,7,3,1,6,5,2],![5,1,2,6,7,0,3,4],![5,7,4,6,1,3,0,2],![3,7,4,0,2,5,6,1]]

lemma orbit (j : Fin 8) : perm j j = 0 ∨ perm j j = 1 := by revert j; decide +kernel

def edgeList (x : Fin 8 → Bool) :=
  ([1,12,23,4,15,26,37,46,57,74] : List Nat).any fun e =>
    x (Fin.ofNat 8 (e/10)) && x (Fin.ofNat 8 (e % 10))

set_option maxRecDepth 5000 in
set_option maxHeartbeats 3000000 in
lemma same_graph : ∀ (j : Fin 8) (x : Fin 8 → Bool), edgeList (x ∘ perm j) = edgeF x := by
  decide +kernel

def renamed (j : Fin 8) := List.ofFn (fun u => input (perm j u)) ++ [neg (input (perm j j)),one,zero]

lemma renamed_mem (j : Fin 8) (a : Sig) (h : a ∈ renamed j) : a ∈ seed (perm j j) := by
  rcases List.mem_append.mp h with h | h
  · obtain ⟨v,rfl⟩ := List.mem_ofFn.mp h
    apply List.mem_append_left
    have mem := List.mem_ofFn.mpr (show ∃ i : Fin 8, (fun k : Fin 8 => raw.getD k.val zero) i =
      input (perm j v) from ⟨perm j v,rfl⟩)
    rwa [raw_id] at mem
  · exact List.mem_append_right _ h

lemma target_in (j : Fin 8) (C : Circuit) (h : FanInTwo C)
    (he : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x ++ [!x j,true,false]) = edgeList x) :
    target ∈ execute C.gates (renamed j) := by
  let w := execute C.gates (renamed j)
  have project (s i) : bit s i (w.getD C.output zero) = s := by
    rw [← b_read]
    change ((execute C.gates (renamed j)).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ (fun g hg => (h g hg).1)]
    have eq := he (sample s i ∘ perm j)
    rw [same_graph,sample_ok] at eq
    simpa only [renamed,List.map_append,List.map_ofFn,List.map_cons,List.map_nil,
      bit_neg,bit_one,bit_zero,Function.comp_def,input,sample,Circuit.eval,Circuit.wires] using eq
  have et : w.getD C.output zero = target := by
    apply Prod.ext
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project true ⟨i,hi⟩
      change (w.getD C.output zero).1.getLsbD i = true at p
      change _ = (BitVec.allOnes _).getLsbD _
      simpa only [BitVec.getLsbD_allOnes,hi,decide_true] using p
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project false ⟨i,hi⟩
      change (w.getD C.output zero).2.getLsbD i = false at p
      have hz : (0 : B).getLsbD i = false := by simp
      exact p.trans hz.symm
  have rep := get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun hn => hn target_proper)

theorem lift (un : Impossible 12 0 raw)
    (hi : Impossible 12 0 (raw ++ [neg raw1])) (j : Fin 8) (C : Circuit)
    (fan : FanInTwo C) (he : ∀ x : Fin 8 → Bool,
      C.eval (List.ofFn x ++ [!x j,true,false]) = edgeList x) : 13 ≤ C.size := by
  by_contra! cap
  obtain ⟨k,t,S,le,live,sub⟩ := extract C.gates _ fan (target_in j C fan he)
  have bound : k ≤ 12 := by change C.gates.length < 13 at cap; omega
  have subset (a) (ha : a ∈ S) := renamed_mem j a (sub _ ha)
  obtain rfl := no_inversions live bound _ subset
  have h := restrict_live live rfl (initial_bound live bound _ subset)
  rcases root_choices live _ subset with eq | eq
  · exact un k bound (eq ▸ h)
  · rw [eq] at h
    rcases orbit j with hj | hj
    · rw [hj] at h
      have e0 : input 0 = raw0 := rfl
      exact low_excluded live bound (by simpa only [hj,e0] using eq)
    · rw [hj] at h
      exact hi k bound h

-- A read-once monotone formula assigns every positive/negative input pair to a
-- distinguishing wire. The pairs assigned to any one wire form a rectangle.
def rect (S : Finset Sig) : Prop :=
  ∃ f : Fin 628 → Fin 628 → Sig,
    (∀ p n, f p n ∈ S ∧ (f p n).1.getLsbD p.val = true ∧ (f p n).2.getLsbD n.val = false) ∧
    ∀ p n p' n', f p n = f p' n' → f p n' = f p n

lemma rect_split {U : Finset Sig} {a b : Sig} {d : Bool}
    (ha : a ∉ U) (hb : b ∉ U) (ne : a ≠ b)
    (r : rect (insert (bin d a b) U)) : rect (insert a (insert b U)) := by
  obtain ⟨f,good,cross⟩ := r
  let g := bin d a b
  let side (p n : Fin 628) := if d then a.1.getLsbD p.val else !(a.2.getLsbD n.val)
  let who (p n : Fin 628) := if side p n then a else b
  let out (p n : Fin 628) := if f p n = g then who p n else f p n
  have pick (p n : Fin 628) : who p n = a ∨ who p n = b := by
    simp only [who]; split <;> simp
  have avoid (p n : Fin 628) (e : f p n ≠ g) : f p n ∈ U :=
    (Finset.mem_insert.mp (good p n).1).resolve_left e
  refine ⟨out,?_,?_⟩
  · intro p n
    obtain ⟨mem,hp,hn⟩ := good p n
    by_cases e : f p n = g
    · rw [e] at hp hn
      have hpick := pick p n
      simp only [out,e,ite_true]
      refine ⟨hpick.elim (fun e => e ▸ Finset.mem_insert_self _ _) (fun e => e ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)), ?_⟩
      cases d <;> simp only [who,side,g,bin,ite_true,ite_false,Bool.false_eq_true,
        BitVec.getLsbD_and,BitVec.getLsbD_or] at hp hn ⊢ <;>
        cases ap : a.1.getLsbD p.val <;> cases an : a.2.getLsbD n.val <;> simp_all
    · simp only [out,e,ite_false]
      exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (avoid p n e)), hp, hn⟩
  · intro p n p' n' same
    by_cases e : f p n = g <;> by_cases e' : f p' n' = g
    · have c := cross p n p' n' (e.trans e'.symm)
      rw [e] at c
      simp only [out,e,e',c,ite_true] at same ⊢
      cases d
      · simpa only [who,side,Bool.false_eq_true,ite_false] using same.symm
      · rfl
    · simp only [out,e,e',ite_true,ite_false] at same
      have h := avoid p' n' e'
      rcases pick p n with q | q
      · exact (ha ((q.symm.trans same).symm ▸ h)).elim
      · exact (hb ((q.symm.trans same).symm ▸ h)).elim
    · simp only [out,e,e',ite_true,ite_false] at same
      have h := avoid p n e
      rcases pick p' n' with q | q
      · exact (ha (same.trans q ▸ h)).elim
      · exact (hb (same.trans q ▸ h)).elim
    · simp only [out,e,e',ite_false] at same
      have c := cross p n p' n' same
      simpa only [out,c,e,ite_false]

lemma tight_rect {k t : Nat} {S : Finset Sig} (h : Live k t S) (ht : t = 0) (tight : k+1 = S.card) : rect S := by
  induction h with
  | stop =>
    refine ⟨fun _ _ => target,fun p n => ?_,by simp⟩
    refine ⟨Finset.mem_singleton_self _, ?_, ?_⟩
    · change (BitVec.allOnes 628).getLsbD p.val = true
      rw [BitVec.getLsbD_allOnes]
      exact decide_eq_true p.isLt
    · change (0 : B).getLsbD n.val = false
      simp
  | unary => omega
  | @binary k t U a b d _ _ ne fresh tail ih =>
    have ng : bin d a b ∉ U := fun hm => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    have size := (live_size tail).2
    rw [Finset.card_insert_of_notMem ng] at size
    have l1 := Finset.card_insert_le a (insert b U)
    have l2 := Finset.card_insert_le b U
    have hb : b ∉ U := by
      intro e
      rw [Finset.insert_eq_of_mem e] at tight
      have := Finset.card_insert_le a U
      omega
    have ha : a ∉ insert b U := by
      intro e
      rw [Finset.insert_eq_of_mem e] at tight
      omega
    apply rect_split (fun e => ha (Finset.mem_insert_of_mem e)) hb ne
    apply ih ht
    rw [Finset.card_insert_of_notMem ng]
    omega

def pRow (j : Nat) : Fin 628 := ([90,0,3,93,1,4,10,14,6,9,11,15,28] : List (Fin 628)).getD j 0
def nRow (j : Nat) : Fin 628 := ([23,142,39,43,55,355,110,130,83] : List (Fin 628)).getD j 0

def alone (v : List Sig) (p n : Fin 628) : Option Sig :=
  match v.filter (fun w => w.1.getLsbD p.val && !w.2.getLsbD n.val) with
  | [a] => some a
  | _ => none

lemma alone_chosen {v : List Sig} {p n : Fin 628} {x a : Sig} (hx : x ∈ v)
    (hp : x.1.getLsbD p.val = true) (hn : x.2.getLsbD n.val = false)
    (ok : alone v p n = some a) : x = a := by
  have mem : x ∈ v.filter (fun w => w.1.getLsbD p.val && !w.2.getLsbD n.val) :=
    List.mem_filter.mpr ⟨hx,by change (x.1.getLsbD p.val && !x.2.getLsbD n.val) = true; rw [hp,hn]; rfl⟩
  unfold alone at ok
  split at ok
  · rename_i y e
    rw [e] at mem
    exact (List.mem_singleton.mp mem).trans (Option.some.inj ok)
  · contradiction

-- Four pairs can force two different wires to own the same pair.
def rectangleCheck (v : List Sig) (p n na nb pa pb : Fin 628) : Bool :=
  match alone v p na,alone v p nb with
  | some a,some b => a != b && alone v pa n == some a && alone v pb n == some b
  | _,_ => false

lemma rectangle_false {v : List Sig} {p n na nb pa pb : Fin 628}
    (chk : rectangleCheck v p n na nb pa pb = true) (r : rect v.toFinset) : False := by
  obtain ⟨f,h,cross⟩ := r
  have one {i j : Fin 628} {a : Sig} (eq : alone v i j = some a) : f i j = a := by
    obtain ⟨hm,hp,hn⟩ := h i j
    exact alone_chosen (List.mem_toFinset.mp hm) hp hn eq
  unfold rectangleCheck at chk
  split at chk
  · rename_i a b ea eb
    simp only [Bool.and_eq_true,bne_iff_ne,beq_iff_eq] at chk
    obtain ⟨⟨ne,fa⟩,fb⟩ := chk
    have ca := cross p na pa n ((one ea).trans (one fa).symm)
    have cb := cross p nb pb n ((one eb).trans (one fb).symm)
    exact ne (((one ea).symm.trans ca.symm).trans (cb.trans (one eb)))
  · contradiction

def digit (code i : Nat) := (code >>> (4*i)) &&& 15
def hintCheck (k : Nat) (v : List Sig) (code : Nat) :=
  decide (v.length = k+1) &&
    rectangleCheck v (pRow (digit code 0)) (nRow (digit code 1)) (nRow (digit code 2))
      (nRow (digit code 3)) (pRow (digit code 4)) (pRow (digit code 5))

lemma hint_sound {k code : Nat} {v : List Sig} (hn : v.Nodup) (ok : hintCheck k v code = true) :
    Impossible k 0 v := by
  obtain ⟨l,test⟩ := Bool.and_eq_true_iff.mp ok
  have l : v.length = k+1 := of_decide_eq_true l
  intro m hm h
  have n := (live_size h.live).2
  rw [List.toFinset_card_of_nodup hn] at n
  apply rectangle_false test
  apply tight_rect h.live rfl
  rw [List.toFinset_card_of_nodup hn]
  omega
def code11 (i : Nat) : Nat :=
  let block := match i / 512 with
    | 0 => 0xdff92dfe929ff929fe92dff74dff14dff97dfe749ff749ff149ff97dfe94dfe71dfe219fe749fe949fe719fe21dff94dff21dff249ff94dff719ff249ff719ff21dfe149fe14dfe97dfe729fe97dff729fe72dfe249ff729fe24
    | _ => 0
  (block >>> (20*(i % 512))) &&& 1048575

def offset11 (i : Nat) : Nat :=
  let block := match i / 512 with
    | 0 => 0x92281f79a5523cc28a248183040000
    | _ => 0
  (block >>> (6*(i % 512))) &&& 63

def proof11 (_ : Nat) : Nat := 0
def roff11 (i : Nat) : Nat :=
  let block := match i / 512 with
    | 0 => 0
    | _ => 0
  (block >>> (1*(i % 512))) &&& 1

def code10 (i : Nat) : Nat :=
  let block := match i / 512 with
    | 0 => 0xcff494523fd45978dfad1d33fd29718ffcd5cb3fd2424cbfb50873fd2f92cff5224b3ff29748ffcd1cbbbd2814cff4a5ca3fef4248f79d05337eb494cff124533fe5414cffba4923fef514cff15452bfd4571ebfb51d3bed24218ffcd0873fc4214cff38c933fcf492cff4d092bff48978ff53e4a3fef524cff495d33fd2874aff8d1cb3fee324afe851d33fd4324cff390533fee914cfe850873fd2571aff524863fd4374cffba09337eb424cff3d252bfe5471cffcd4933fe42218bfb50873fd2e14cffcba533ff2871cff388923fd49718ff50e533fce924cffca5c73bf2914cffd0c933fee224edfad1d33ff2972cef924533ff2f94cff491c73fd24748ff5264b3ff4594aff4d4522fed471cffb94933ef2492aff3d4873ff2f24cfb951d33fce3148ff4d4923fcf4148fe850873fe34248ffd0a4b3ff2874cffd15c73fce824cff495cb1fef421cffb8c533ff2e928ffbd24b3ff2494affcd053bbe2814cffb94533fd3574cffcbc533fce521cfe851cb3fd4574ebfb51c6bff4892cffb90933fd3572cffcb8933fce374cff251cb37eb421efed025f3fd2f21c7fb95c73ff2594c7fcbdc6bfd3521affcd0933fce914affa50863fe3474cff954533fee374ef79d086bfb4097aff8d252bee5474cffc94923de74748fe851cb3fee271cffb95d21fef421aff150533ff4372cff151c6bfc5514cffc924b3fd2814cff951d23fcf424affbd2523fe9471cff390873fef514cffba1d33fef4248ff53e52bfd34728ff50dca3ff3574cffc90933fce2748dfad086b7eb424e7f4b9c73fd2e21cffbd087bef2521affbd487bbe9421aff3d4933fd4997af79d0873fee2748ff950533fe48148ff50e4abfe5494cffcbdd33fef524aff4d5cabfd3424cffb91c73fd4921cff4b9cb3ff3471e7f4bdcb9ff2e97aff951d33ff2514ef79d0533fee571cffcbdc7bf6e314aff5265ebfd3574ef79d1d33fd3524aff515d33ff2f72cffcd0533fc4814cff150533ff3474aff50e5ebff44978ff4d5c63fef421cff4a486bbe94218ff3d4523fd4594affbd0533f634748ff8d1cb3fcf521affd0a5f3fee4748fe851d33ff2e74aff50c933ff4374cffc95d2bf63474aff3d0873fd2414adfad2533ff2471cff8d1cb3bd28148ff951c73ff4574cffca486bff3524cff8a0533ff4897cffd25c73ff2571cfb490863fd4571cbfb51d2bfe3424cff90c923ff4897cffc95caafed474aff954533fd4374cdfad1d2bff3474cffd264b3fd3474cff494873fd4972cff4a0873fef492aff4d1d33fe4314cffba052bff3471cffc91d23fd4921cff5165f3fe4224cff388533ff3572cff4a1cb3ff4597cffca087bbd2924efbb94933fef414aff525cb3fee214efe851d3bee4221cff3d092bfe9472cff10c933ff2f92cff4ba533ff2872cffd25cb3fc9471cffba486b7eb474cff53e533fd24218ff4d4533fef521cffd3e533fe94218ff3d4873fce524affcd1cbbbf2894affbd0933fc4314cff4be53b7eb494cff3a0523fb4097affbd452bff3421cff525c73fd2472cff250873fc4224cff4bc923ff3414aff53e4b2fed471cffb90533fd2e928ffd224b3ff2e14aff5165f3fc3474cff390933fb4097affcd5cbafed421efe850873fd2f14cff38c86bfd43748ff4d4863ff3424edfad0933fd4f928ffa5086bde7414cfbc94873fd2e24cf79d0863fe3494aff525c63ee5474cffb8c873fd3472cff51652bfd4394eefca4533fee5218ff150533ff4f928ff4d5cb3ff2f21affbd4923fc5514cffcd5d33fce5148ffbd2533fd4497effb8c93bbe4914aff5264a3fd4997efbc924a3fd3472efb951d33ff2414cff3a4873fee821aff4d492bfcf414cffd2486afed421afe8508637eb424cff3d4531fd2e71cff388863fef521e7fbd0873be94218ff3d4933fc54748f79d0873fd49928ff952539fee271cff395d33fee221effb94533fe94718ff4d0933ff2894efe851cb3fce471cff3d0871fd2f72cffb90871ff2e97cff4bdd33fd29248ff951d33fe3474cf79d0533fce571cfdb8c539fee571abfb51c73ff4497cff4b9c63fd3574cf79d1d2bfe3474cff0d1ca3fd4574cffb91cb3fd2494cff3a086bff4292cff50dca3fd43978ffd125ebfa1472cff4bdc73ff4997affbd24a9fef421cff4a4523be94218ffbd0533fd2f728ffd0a5ebfcf424cff4a0933fce4748ff50c923f63474cffcb8863fcf421cff3d0533fef494cffc948637eb494edfad086bfd4f94aff50dca3ff3524cff494933ff4892e7fcbdc6bff3574cff4b9d2b7eb421cff515c73ff2e728ff8d092bde7474aff950522fed4748ff95452bfd4392cffca4933fe4824cff5225e3ff3474cffcba5f3fe5494cff951c73fc5494cffa51cb3fd2594affa51c63fd3474cffcd0923ff3471cefca2533fe4214cffcd0873ff2914cef4a4933eee524cffcd1cb3ff2824cff3d4933fc3424cff92452bfd3571cff4a5d2bfef4218ff525cb3fa1474aff3d4523fe9472aff516533ff2472cff4a1c7bf63474
    | _ => 0
  (block >>> (30*(i % 512))) &&& 1073741823

def offset10 (i : Nat) : Nat :=
  let block := match i / 512 with
    | 0 => 0x3c1dfef777b9d9eb753a3cee5f1b8dc5e1f037fbede6e771b8dc6df65add66a751a8d469b45a2d0e873f9cce6672f92c863b1d8ac3e1b0b82c0dfaf97bbcddeed74b8db2d368b3d8ac15faf56eb556aad56a552a85429b49a451687419ecf273389a4ca6330984b2552a9349649219047239198b452230e8642a15078240602ff7dbe5f2f97abcde4ee76bb5d8ea74b99cae370b81b8dc6d35daad369b4d9ece653218cc5612fd7abb5c2dd6cb55aad566b056ab55aa751a85409d4ca612e9649a39188b44221108743a00fa793b9d8e671389b0d4693298cc4622e96cb255291449e4d249208843211007a3c1c8dc6c35188b0582b148a04e2511080401e0e86c2e170b0502412090401607030100000
    | _ => 0
  (block >>> (9*(i % 512))) &&& 511

def proof10 (i : Nat) : Nat :=
  let block := match i / 512 with
    | 0 => 0xc3271a851572851372c3271a8515722c75289113820735839113828515722c75289113828515725335665325662c7328851572533566c3271a8515729113828515725325668515722c75288523728515725335669113822c75285325668515722c75288515725325662c65289113828515728515725325669113828515722c75285325668515722c7528851572533566532566c3271a8513728515729115828515728515725081718515728515728515728515728515725325668515729113828515729115828515728515728515729113828523728513728515720725839113820727839115828515728513722c73288515728515722c73285325662c75289113822c75289113829115829115828515728513722c75289113820725832c75288523722c7318911382851572533566911382c3271a9113820725830725438515728513722c75288523722c75289113825325668515722c7528c3271a8523728515728523725325662c75288515725335662c75288515729113822c65280725838515725335669113828515720725839113822c73189113828515722c75289115828515722c7318c3261a9113825335668515722c7528c3271a9115828515722c7528851572851372852372851572533566533566240131911382851572072583c3271a9115829113828515725325669113828515722c75282c75282c75289113828515728513722c75282c7528c3271a851572c3271a8515722c73289113828515722c75289113828515728515722c7528c3271a851572851372911582911382851572533566851572532566911582912382851572911382851572533566532566
    | _ => 0
  (block >>> (24*(i % 512))) &&& 16777215

def roff10 (i : Nat) : Nat :=
  let block := match i / 512 with
    | 0 => 0xcbcac8c5c3c3c1c0bbb9b9b7b7b4b2b0afadacaaa9a8a7a5a4a3a09f9d9d9a9897959594939291908f8d8c8a88878685838282817f7b7a787777767473726e6c6b6b69696665615e5e5c5b5a585552524f4e4b4a494644413e3e3b39363533302e2d2b262322211d1c1a171412100d0c09080706040000
    | _ => 0
  (block >>> (8*(i % 512))) &&& 255

def code9 (i : Nat) : Nat :=
  let block := match i / 512 with
    | 0 => 0xc3fe6ef421d5bcead421c7bceae414c6fe52b494c6fdc6b421e7b4ea142187f86e9472c5f8aad474c77dea9421a7f42c9421a7dcace814c6fad2b474c7be5e7474a6fd6c421487facaf494c7f06e147296fd6d3514a7f42c9472c7bceae874c6f86eb421a6fd6ce82497f42d3472c7e9ca347487fded432487feace41487fd2cf521c6fdeeb424d7ccaa347487fa6e551495fdac5414c3f9c6f42187fee8e224c7f6521421c57daa942187f9ee942187fead2972c3f9d2f421c7f06e147487faac481487fa6ef424c3f9caf421c6fd6a942187fdec5514e5bcead42197bced432487fee92e2467f1ca1472a7bcec4314c6fd6c5414c7ba4a7421c7f46a147297f42d4392c5f8aed421a7f6c12e72d2fdeab42187fa6c5514c7f5ee1472a6fd6c4914c6fa4ab424a77ed12514d5edaa3474c7ba6e7421c7f1ca1474c7f6df4097c6fa52b474d7d24a142107fee92814a77d2ce324d7d4aa147487faeb2f24e6ec6ab474c7f5ee1474c3fa5ef492c7f42d3472c6fe4ab474a6fd6d2821c7bceae21486fd6c5414a6fd6c5471c7bad27414c5fdaa347485fdacf514c5fe52d421a5fdac942196fd6d4992c7ead2347487faeae324c6fa6eb421c7bec6741467b8527414c7bce8e821c7d9ca5474c3fa5ef494c7be5e7421c5fda83474d5f5aa1474c7f1ee1472c77aea4914c6f9cab42195fdad4392c6fe5eb424e6f56a1474c7f42d3474c7bceae821c7b4ea142167f0861421a77d2ce514a7bcec5471e2fdeab421e3ddcae324c5f9c6d474c7ba5e7474c6fdd2b42487f42c5414c3fa5f3471e7d24a1421c7f1ee1421a7fc6d2972c6bceab47465f9d2d474a7bcec3472a7dcace324c5fcaad471c5f9cad474c7f1ea1421c6fe52b47487fac6f524d5dcaad474c3fe5ef414c7dcacf41487fe6d4972e6dcaab474a5fdace221a7bcece924a6fd6d297297eaeae314a7f42cf41487fded352487fded492187fac6f414e3ee5ee314a7dcac9471c5fad2d421c5fdacf51487fe6ef421c3fad2f421c5bcead421a7dcac3474c7f486142187faeae314c7be6e7421c7f66a1474c5f8aed474e5da4ad421a7f42c5414c7f66e142187fe6c5414a77a6e2814c6f9eab49496fd6c5514c5f9ead421c7f5ca1421c7bce8e41487fae8e814c6fa6eb49486fd6d3514a3fadf2572d73cea942187fded499287f42d347287fded351487fcad351487f86cf51485fdac541495fdacf424a7ec6ce821c7de6a5474c7da4a5494c7ba5e7421c7bade742187f92cf514c6fa5eb42487fe6cf51487faeae321c5fc86d421c7f46e142187bced432487f42d4392c5fed2d471c7bac6742196fd6d4392a6fd6d2971c2fdeab42187faeae414c5edaa347487facaf424c7d24a1421c5fdcad421c5fed2d421c7f6c14f92c5fe6ad474a7f42ce821c7dcacf524c6f9eeb424a6fd6d2814c5fad2d474a3fdec4224c77e529471977d2cf421c3fac6f421c5fdead421e73cea9421a6fd6d3474c7ba527474c6f86eb474c7bac67414a5fdac541485fdad439786fd6d4992c6fec6b494a6fd6c5494c7f5c61421a6fd6ce92187faeae22487fcad4997e75a52e524c5f5aa1474c7bcea5474c6f9eeb421a7f42c4214c77e529421c7f4ae147266f886b42187fad25471c6fdcab474c7f46e1474d6dc86b42187fac6f42487f9ee342487f9ee5414e6da4ab42187fc6d4574c7bed2742197ec6cf424a7bcec4224c5fa6ed471a7bced3474977aea4914c5dcaad474c7bad2742196fd6d4997c5fe6ed471c7f6c74097c3fde8942187fc6cf42487fdec5414e67d6d292487faeb251487fa6ef514c5fdc6d42187eaeae314c7be527474c6fa6ab47487fa6ef414c77d2cf42187fe6e947297f42cf421d3f5ea142187fad3347487faeb2f2187faeae574a5fdace82487fad2f421a5fdac4214a6fd6d2872c77a514971c7e8aa3474c6f8aeb42187fee9241487faeae374a7f42d3472c7ba527421c77dee942187fad3449787fe6cf42187fee92f2496fd6cf42487f6c13571c7be4a7421c6fa52b42487f8ae3474a77ed1249496fd6d342486fd6c5514a7eec52f14a7bcec3424c77e914992c6fe4ab424c5fac6d471c73cea94216778869421c7bce84214a6fd6d489796fd6cf41497f42cf414c5fdaa942187f9ed4921e75a4a942185fdacf424c5fda89471c7f1ca1421c7f0aa1474d1fdead421c7bede7421c7f2cb4097a7dacb2821e3f5ea1421c779ea9421a6fd6ce81497f42d3474d6f56a142165f9c6d47197bcecf414c5fdacf424c6fed2b49487fe6e5414a6fd6ce92486fd6d4392c6f8aeb49497bced4971a7f42cf52487facaf514a3fadf2871a5fdace274a7bcec5474c7f42cf421e3f65f4097c6fc6eb421c6da4ab421c7be52742187f92c5514c3fa9f2f9495fdad3474e5f5aa147487fac6f421c77c869421a7bced4897c6fe52b424a6fd6c3424c5f9cad42187fec9357487fdee5414c7ec683474e1fdead421c77dca9421d7e46a1474a3fdec4314c3fa4af421a7f42ce514c5fe6ed42187fdee551493fdec5414a5fdad4372e5dcaad474c7e9c63474c5fdacf414c7f46a1474a7bcece92147fee92814a7f42c547467e9d2347487feea491487fe6c551487ec6cf424a5fdac9471c7f2d21474c7bceae474c7f06a147487bced4394c7da4b3421a7f42ce471877aea4914a5fdac347486fd6d4997a7f6c12e7187fee92e14a7dcad3474c3fe5ef421a7f42ce474c7ec6cf42487fad2f492c7dcaa3474c7f1c61474c7f65e147287facb4897a7f6c12e74c7f5ee1421e67e52b494c3fdd2f421c3f5ea1421c7f65f4097a6fd6cf49467f1d21474a7f42ce574a3fdec9421a3fe6ee571c7bade7474c7dca83474c7ba6a747487fec94f94c5fa5ed471d4fdaab474c77dc69421c6fad2b42486fd6cf424a5fdac9472c7d9c65474a5fdace914c77d2c5514c5fa4ad47487feace821c5fed2d474c6fcaab474c6f9c6b421a77d2c421487f8ae947167d9d2547486fd6cf41487f42cf414a3fded297187fad2f42487f9ee5514c7f42c5414c7de5e5474c6fd6cf424c6f9d2b421c7bcea4221c7baca7414c7ddd25474c1fdead421c6fd6d4992c6fc86b424a7bcecf494c7bceae27487fcacf41487f42d3474d7d4861421c7bceae42187feace324a77d2c347287bced497187feace514c6fdcab424a7bcece814c5fe5ed474c7ee6a347487fee6f524c7bceaf421d37dea9421c5fdad3474c3fa6ae571c5fdd2d474c7beca7474c6fc6ab424a6fd6cf414e73a527414c3fa6ef421c7bce8f414a7dcad4897c7f25e147297f42cf524c3fdcaf414a77e6e491465f886d421a5fdace224c7f6c13571a7bced4971c7e46a1474c7f4ae1421a7bcecf42487fed2342487fded3521c6fe6eb42487fa6e5414c7bce8e214c7f25e147497f42d457187faeb2974a7ec6c9472e3edcae314a7bcecf414c5fdac5414c7bce8e81487fad25414c6f8aab494c7f42cf524c7f66a1472c779ca942187fac65414e37dea9421d7b4ea147495fdacf421d67d6a9421c7ccaa3474c6f86eb424c7f4289421c7da5e5474a7f42c3472c5fa52d471c5fcaed47187fac65474c6fdc6b424
    | 1 => 0xc6fc6ab47496fd6cf421c5bcead47497bced439287fead257487fcad3474c7be4a7414c5fec6d471c3bceaf421d4fdaab421c5fe52d474e6f56a1421c6fa5eb494c7f24a147287fee92e21c7edc63424a7dacb2f92d6f56a1474c779ee9421a7f42d4497a7f6c12f14a7f6c12e92a6fd6d4972c77d289421a6fd6c5514c7bce85414c7f2d34097e67ed2b494c77e692924a7f42ce914c7f6834897a77ad32f9487fed13572c7f24a1474c6f9c6b474c7ee5e3474d7742a9421a7f42c3424a7ec6ce514c7edd23474c6f9cab47487fd2d4571d6dcaab474c7f25e142187faeae524c5fac6d421a77ad3259485fdad437287fad23472c7f0ae147467b8867421c3fdea4221a7dcace914c7da4a547497bcec541487feace921a7f42ce521e4fdaab42187f42cf421c6f886b424a6fd6c4314c3fa5e5471e79a4a7421c6fa4ab421c7f65e147497dcacf414c6fd6cf421c3fecaf421a3fded2571a7f6c12f74c7f2d21472c7bce8f421a5fdac3472c6fac6b494a5fdac5474c7f5d21474d57daa9421e7742a942187f9ef489286fd6d3424c7de6a422147faeb2914c7dac65474c5fa5ed421c6fed2b474c7ba6e7474a6fd6d2824c7bce85474a5fdace32487fa6d4574c6fe5eb421a7bcec9421a5fdac3424c7dcad347417fee92814a77d2c5471a77c6d292487fd2d437287faeae924c6fc6eb424c3fe6ae27196fd6c5414c6fdd2b421c6f56a142187facaf41487fec9357187bcecf414c7baca7474c6fdeeb474c6fe6eb494a7dec92e92c5fec6d474c7ea5e3474e57daa9421a7f42c4224c7f26e1472c7bede7474a5fdace921c7bcea281487fa6e9472c7ba4a7414c6ec6ab47487facb3471c6fd6d3514c5fdeed474c6fe6ab474c6f8aeb42487fee9247485fdad347487fdee9421c7f66f4097c6fe4ab494c7ba6e7414c3fec6f42196fd6d347487fad2f521c5fdcad474c3fdec5414c7f6cb4097d7acea3474a7ec6ce92487fa6cf521c7e8ae347487bced439287f9ee549487faeb257487f86c5514a3fdec421487fed14597a7ec6c5474c4fdaab421c779c69421c7f66e1472a7da6e4221c7bcea3474c7f252142187fadf3414c6f56a1474a3fdec432483fdec5414c7f6d3409787fc6d4972c779d29421c7f2d21421a7f42ce524a5fdacf514c7f64a1421c77e5e9421c7be5e741487faace221a5fdac4224a6fd6d4997c5fa6ad474a7f6c12f24a7f42c5471c7bce83474c6f9eab424c7742a9421c77dd29421a7f42ce924c7bceae814c3fdea9421c6fe6eb421c7bceae22197bced347487faeb2f1487fed14f92c7bce8e274c6dcaab474c5fdeed421c6fd6cf414c7f42cf414c6fa5eb421a6fd6d4992c6fdeeb494c5fa6ed47467b9d2747487fec65414a6fd6c547487bcec5414c7f2df4097a6fd6c947187fa6e5474c5fa52d421a7dcace924a77ed12e94c5fdc6d47487dcacf414c5fe4ad421a6fd6c3474a7f42c3474c7beca7421a6fd6c432487fecaf424c77a514921c7bcecf414c77a514324c7de6e5474a5fdace814e67d6a9421a7bcec9471a77ad32e14c5fad2d471a7bcec347487fded4594c7ea52347487fcad497187fa6cf514c5fe52d471c6f9eeb474a7bcec5414a5fdacf424c3fe692f72c6fe6ab424a5fdad3474a6fd6d2914a7dcacf414c6fa4ab494c77a5e9421c7ba5e7414c5fcaed474c7ecaa3474c77e6a2814a7f42cf492a77ad32414c7f1ee1474c7bce8e22195fdad439787fae8e82497bcecf424c7ecae3474c6f9c6b424e76dc64914a7dec92f24a6fd6c347287fd2cf421c7bce8e421c6f9d2b424c7bcea4814a3fa6ee27187fec6f41486fd6d347487fae6f521c6f9cab424e5f5aa142196fd6d4972d6bceab421c7acea347487f8ae3424a7f42c4314c7f24a142187fa6cf524c7f4aa147487faeae91487f92d4324c7ee523474c7da485514c7f26e1474a6fd6d2921c6fa6eb424c7bec67474c7bced4324a6fd6c5414c7bed27474c6fa52b42197f42cf42487f9ee347487facaf421c7f6521472c77e6e9421c7b4ea1474c67d6a9421c7bcea5414a7f6c12f94c6fcaeb494c7da494571c7bced3474c7baca7421a7f42d489787bced3474c7f652147487fe6ef414c5f8aad471c7dec6547495fdacf414a5fdac431493faeae571c5fa4ad421e6bceab421c3fa9f2f92a77d2c422497dcad3474c7beca7414e4fdaab474c7f42a947297f6c1357187fadf352487fd2d3472c5fdad4372c79cea5474a5fdad4897c7f26e1421c7f68b409787fee92872c77a6a4914c7f5ea1421c7de525474a5fdace321c6fc6eb474c5fdeed47197f6c14f92c6fe52b421c5f8aed471c6fad2b494c7f0ae1472a7bcece824c7bede7414a6fd6cf424c5fe5ed421c77a6e9421c7ba527414c5fdcad47187f8acf524a6fd6ce914c6fa4ab474a6fd6d342487faeae821c7be6e747497daeae524c7f26a1472c77e4a942163f886f421c6fdeab424a3fadf2972c7be6e7414c5fdd2d421c5f5aa1421c3fa5cf521a7f42ce421c7f28b4097c6f9eeb494e3da4af421c6f86ab47487feeae914a7f6c12e21c3fa5ef424d6da4ab421c7da8b2594c3fde8f421c5fec6d421c6fad2b421c77a525414c7f2c74097c7de4a5471c7f06a147297bcecf421a6fd6d2924e7acea3474a7ec6ce92187fe6ef42466f9d2b47487bcecf424c7be4a747487fcacf514c6fe5eb474c7ddca5414e76e52e314a6fd6cf421c7edca3474c6fdd2b474a7dcace82187fad3357287fad2f414c7bcecf424c7be52741486fd6d4972c6bceab421a5fdac5471a7bced4324a7f6c12f2187fcad437487f6c14f9487faeb2924a7f42c4324a7f42cf494e1fa5ed471c5fdc6d471e7b4ea1474a7f42ce921c7f5ca1472c6fd6d3424c6f9eab42197bced4394a7bcecf42166f892b42487faeae514a7f6c12f72c7f46e1472c5fdaa9471a5fdace821c7ea6e3474a3fdec3424a5fdace214c7f5ca1474c7f42a942187f42cf424c3fa5d437287fe6cf41487f9ee5471a5fdacf494c7bcecf421e79cea5474a7dcace921c7f42cf42485fdacf41483faeae571c6fc86b421c7da6e547487dcad3474c7f6814897a5fdac4324c7daeae524c7f26a147495fdacf514c6fdcab421c7eaeae31487f9ee547487fad33424c7f4289472e5bcead474a77aea4914a3fec52f72c77a4a9421c6fdeab421c6fcaeb424c7bce89421c6fa5eb47487fadf3421a7ec6ce81487f6c14f92a7dacb2e21c77a53341487facb3414c6f86ab424c5fcaed421c6fdeeb421c6fe6eb474d7b4ea1421a7f42ce57187faeae521c7da6a5474c7f06e1421c77d2d432486fd6cf421a7f6c12f71e3f6c12e7197f42c541487daeae524a5fdacf414c6fa6ab42487fa6d4972d6bceab474c7bac67474c7f5c61474c7ec6cf514a7f42ce414c6fed2b421a6fd6c9421c6fd6c5514c77a529472a7bcece914c7ba4a7474a7f6c12e14c5f9cad471c7bad27474c7f6d21474a7dec92f21a7bcec9472c7dca85474a7f42ce814e3f6df4097a6fd6d4892c6f8aeb474c7bcea4214c3facaf42187bcecf421c7f6d21421e75dca4914c7bcec5414c5fe6ed47487fe6cf524c7ddc65474
    | 2 => 0xa6fd6ce821c5fe4ad471c7bec6742187f9ec5514a7bcec421487f9ed4324a7f42cf424c7bce8e474c5fac6d474a7ec6ce824c7f66e1474a6fd6c9472a7f42c947187fed2f414a6fd6c4814d79cea5474c6fcaeb474a7bcec4324c3fdc6f424a3fdec5414c5fa5ed474c7d4aa1474c6fc92b424c4fdaab47487faeae571a5fdacf421a7f42ce424c7bcea9421c5fda8942187faea4314a7dcad2921a7f6c12e24a7f42d3474d5bcead474c3fa5cf514a5fdace924a7f42ce824d3bceaf421c7de4a5414d5f5aa1421e6bceab47487fdee3424c5fdacf421a7dcad2972c7ee4a347485fdad4392a77ad32f24c3fa52f421a7dcacf494c7f2521472c3fe4af421a7dcace824a7f6c12e94c7f64a147287fae6f524a77d2cf421c6fd6d4997e67d6d2814a6fd6c4224c7f2521474c37dea9421c7bed27414a7f6c12f92a77ad32524e7e46a1474c7bceaf414a7f6c14f94c6fd6d497287feeae32187fe6d4574c6fd6d3474c7f64a1474c6fdeab494c6fcaab49495fdad4372e3bceaf42187fc6cf524a6fd6d2871c5fa6ed421c3fe9d4f92c7be6a7474e3da5ee52487fded342487f42cf524a7f6c14f92a6fd6d2874c5f9eed42197f6c14f94c6fe5eb494c7bced4971c7da52547487f42d4571e7ccaa347487fed25414a6fd6d2974c7de4a5474c6f8aab474c6fa6eb474c3fe52f421c6fe4ab421c7f0ae1421a5fdace314c5fa4ad471c7f1c6142185fdacf421c6fcaeb421a3fadf247187fe6e5474c6fdc6b47487faea4914c7f1d21421a7ec6cf424c5fa52d474c7f65e1421c5f9eed471c6fd689421e5edaa3474c6fed2b424c5fe4ad474a77ed12f14a7f42d4571e7d4aa1474a7f42cf421c7bce84814a7fec52f24c7f4ae1474c7f5d2142187feeae924c5f9eed474c7f6d2147287faeb2972c5fcaad47487faea4324a7bcece821c7f6c14f94c5fe5ed471d6ec6ab474c5f9c6d421a5fdace374c3fed2f421877d2cf421a7ec6ce914c7ea4a3474c7dad2547487faeae921c5f9d2d421c7f26f4097c7f42d4571c7bade7414e3f6c12f7287facb3574
    | _ => 0
  (block >>> (40*(i % 512))) &&& 1099511627775

def offset9 (i : Nat) : Nat :=
  let block := match i / 512 with
    | 0 => 0x81b03604c0680b009ffbfe7fafddfbbf67e8fc1f6beb7ccf89ef3dd7baf69ecbd97b2f5deb3d37a6f49e5bc878cf0de03c077aef1dc3b7768ecdd93b075ceb9d6bab74ee99d33a6746e81d039c72ee59cab93724e41c6b8970ce0dc0b7e6f4de1bb3736e4dc5b636b6d0da1b2b606bad69aab556a2d3da5b4a694d21a3344680cfd9eb3a670ce19b333666cc195328650ca193b25648c8d91b23646c818f31d638c658c31662cc5989b0e61ac2583b05606c01802ff5fabed7c2f75e4bc5772ed5d6bad72ae55c8b8d71ae35c2b816fadd5b6b596aad059cb2d64ac758cb15622c3580af95e2ba570add5b2b3562abd572a854aa8d4fa9b532a614a292522a4546a8c512a2144285504a013f27e4fc9f13ca774ec9cd392714de9b133a674cc9913025c4b29592b2564a694928a4f49e93525a4a49291d2324548890920a4047a8e51c2354648c11722a44e89910a204368690ba154208390620941081d02204406801001fd3f47e8fc9f53e87d0f91f03e07bcf59e73ca780ef9de3ba76cec9d53a873ce69cb38c710e09bc3726e0d91b23606b8d61a934c698d29a4342678ce99a32a648c898e316624c4186306604c017e2f45e8bb9752e85c4b89702da5a8b49672ca58cb19622b856cad1582aa550a915029e534a594b29251ca29452844fc9f13c2724dc9a1312584b095927248490919222404808e91d2384688b9142264408690c2164288510620c410800fb1f63dc7b8f41e03b8770ea1d0394720e11ba3686c0d61a433c670cd196324640c61823045f8be1782e45a0b21602b8568ac156298520a3146288508a013a26c4d09912e254498921202384688c114224440861042044007e0f41dc3b0730e01b4358690d019c328620c21802e85b0b615c2984f09a1302504a090118218410820fc1f03c0740d81b0350680c81882f05c0b01602a0500940f81b03405c0a0120200380680d0180280480700c01000800
    | 1 => 0x49792d2564949091b22243c8390720e404808ff1fa3e47b8f31de3b4728e11b63646c8d51a2344688d119e33c658c718e2fc5c8b31562944f89d12a2444889110e2043f87b0f21d43986d0d61ac3185f0be16c2985109e11c2184306e0bc1682b0520a41282304207c0e
    | _ => 0
  (block >>> (11*(i % 512))) &&& 2047

def proof9 (i : Nat) : Nat :=
  let block := match i / 512 with
    | 0 => 0x8510725308660605438515728514828513822c80288515728510722c75282c85288515728510728515728523728515728513828510729110828510728120828523728515728510728110822c8028240231951482851572851572530866508171c3271ac3261a9514829115828515728515729515828510725308668514725308668515728510728523728513828515728560728523728525728515728110822c84182c8018851572851382851072530866851582851572530866851572851072851572851382530866c3261a8513822c80288514828513828510722c74288515722c80282c75288515728513828510728515722c65180c28748515725308660735838515725308661672058510722c8028264135851572c3271a8513828515728513825308662c75288523728513828510722c7428851572852372851572851382851572856572851382851072530866851072c3261a851572856572851382851072c3271a8510728513828515728525728510728513825308668515728513828510728110828513829115825308668510722c7528851572c3271a911582911382851572851382851572851382851072c257288515728514728510828510728110828515728514728513828510722c75288513728515728510728113828515728515728513828523728515721681058515725086710605838515728513822c80289110822c751891158285157285138285157281108279804b851382530866851572851382911582851572c3271a8515728513828523722c7428851072851072c3261a8110828520728515728510728510728515728515828513828510722c65288510728513828510728515722c75280735835308668515722c80288515728513828515728515728510725308662c75282c80188520828515728513828510728113820605838510728515728513828515728513822c70288515728515722c7528540151851382851572851072c3261a851572851072c3271a8525728513828515728515728513828515722c75288515728513828510725308662c74288513822c6528911082851572851072530866c3271a8515722c75288515728510722c7528c3261a851072851072533866852572851572851072530866951582851382530866851072c3271a5401512c80288514728510725308662c75188514722c80180607838515728520728515728515725308661681058515728513822c80188515728513822c75288515728513728510729115828515728513828510722c7528851072c3271a268135911582072543852372851072c3271a851382851572851572851082811382530866c3271a8520728515728510728515728513828515728120828513828110828513828510828510722c75288515728513828510728113822c74288515728510722c7428c3281a8523822c8018911582851382060783c3271a8515728510728515728513828515729115828515728510728515728510728513828510725086712c75288523728513828510722a7028851572060583851382c3271a8515728513825308662c7528851382530866c3271a9514829115828510725308668515722c7028240131851072c3271a912582851572851382851072811382851572951082851072851572851072c3271a2c74285308668515728510728510728513828510729514829513822c84282c75288515728513822c75289514828515725308668515728513822c80282c75288513828515728513828515722c7528530866851572851382060783852472851572851572851072c3261a5308668515720605838513825308663401302c75288515728510725308662c80288513828510722c80282681358515728510722c8028951482851382851072c3271a85257285138285107285157285138253086691158285138285237286084a530866c3271a8515728513828513828513828510728110828523729514829115828510722c74288515729115828523728513825086718513828110822c70288510722c73288515728120825308662c7428530866c3261a8515728510728515728513825308662c70280605838513828510728510729115828523728520728515722c7528
    | 1 => 0x8560728515729115828513822c80188515728113828523728515729115828513828513822c80182c7528530866851072811082530866851572851382530866c3271a8513828515728510725308668515722c75289165828525728515722c65188510728515728513822c84282c75288515728510725308668515722c84182c7528851582530866c3271a8510728515728510728523728515729115828510723481302c75280605838515722c7528852372851382851072530866851572851382530866c3261a8510728110828523728515728510722c80188510722c8028c3281a9514828515728513828515728110828525728520728510725308668515722c80289515828523828510728515722c8018851382811382851572851072c3261a9110828514828514728515728510722c75288515725308662c74288515728514828510728515728513822c70282c6028265135851072530866c3271a8515728510728513822c7528851572851372851572851572c3271a2c8028c3281a8513828524728513828510728113828510728515725308662c80288515728515728510728515725308669115828510728113829115828513828510722c742894174c8513828510720605835308665308668565728510728510720721438514828510728515728520728515722c80188515728513825308668513829515822c80188515728513828510722c75288513828510722c75288515728510729115828515725308668515825308668525728110828523728510728514828510728515722c7528851382951382851072240631851382851072c3281ac3271a8515728510722c75288515728513829115828513828513828515728513822c65180721838515728510725308668524722c7528951482851572851382851072530866c3271a5308660605838515728513828513828510728110825308662c75288524725081719515828515725308660735839115822c7028851572851382811082c3271a5308662c80188513828510728515728520728513828515728514828510722c8018851572851072533866c3271a8515728513822c7528852382851582c3271a8520728513828510728515729125828515728514725081712c80182c7428851572852072851382851072851572851072851572851572851382268135c3271a8515728510728515828510722c65288515722c70188113828515728510725308668513828520728515728514829513828513822c80288515729115829113828120828515722c7428c3261a8515728515728513828515728515722c75289115828515728515728513828513828513828510728523722c80288515728513828515722c75288510722c80281681058515728513828510728515723481302c80289513828513828510722c80289115828513825308662c80180605438513822c75288560728510828510728520728515725308668514728510728513828510728515728515722681359125828515728110822c8028167105852472851382851072530866851572851072c3261a8525728515728513828560728525728523728510728110822c75288515728513828510728523828515728510728160829113825308662c75288513822c8028c3271a2c7528811082851382c3261a8510725308668510728513822641358515722c75282c75188515728513828510725308668515728513828510728513828113828515721681058510728515728514828515728513822c75288510728110828515728510728110825308668515828515728525728523728515728513822c80185308662c75288510728514722c80288513828510728515728510728523728510728515725308668510728515728514825081718560728513828110828515728513822c75288515728510722c7528c3261a852572851072268135c3271a8510722c8428851572911582851382851572851572c3271a8525728515728513828525728515722c75280605838515728513828110822c80189115828515725308668513828515728510722c7528c3371a2c752885237285207285157297084b8510729115828515725308668515728515722c8028c3271a851572851382
    | 2 => 0x2c7428c3261a8515725308668515721681055304668515729110822c80288515728510722c74288510728515722c6518072143c3271a8515728513828510722c7528852372851472530866c3261a2c7528851572851072c3281a5308668515722c75280735438110828515728513820735830605838513821671059115828525728513828515722c80282c75188515728113825308662c70288513728510728513828510728515728515728514822c7518851572851382851082c3261a8515722c70282c75282c8028060143851572851382851572852482851572c3271a87084b8513822c7528c3271a5308662c70288515728520728513828513825335668513825308668515728560728513829115828510729115822c7528c3271a8523728515728510722c75288515722c74280605830605830626838513728513822c75289115828515728513822c7428912582852072851572851572851382911582851482851382c3261a2c75182c73288515728514728110822c7528851072c3281a8560720605439515829115828513828510728110825308669515828515720621438513822c7428851572851572851072c3271a8510728110829115828520828515728515728515728520728515728515725308668515728513828515728513828510728513828510728110828523728513828513828510722c70280605838515728523722c8028c3261a8513828510728515725308660735438510722c75288510728515728513822c7528851572851382851072530866c3271a8560722c7428851382851072500171852372851572851382811082c3271a851072851572c3271a062143851572851072c3281a9115822c7528851072c3271a8560728510725308668520728510725308665081718510725308662c8428851572530866851572851072851572851572851382c3271a8515728515728510728515728514728523728513828510722c75289115824220318525728510729514828515728513828515728513822c75288513825308662c75288515728513828515722c85288510729115828513828510729113828515722c75289113828523828510728515728513828510725308660721839113828510725941825081718515728510728515728513822c84188515728515728510722c75288510729115822c80288515728510728515722c75282c75288515722c74282c80282c7528c3281a851572851382530866851572851382851072851382851572851572851072c3281a8510721751058513823481309514828510729115828110828510722c80288513828510728514728513828513822c65188515728515728513828515728510728110828524728515728513828515728513828510728515728513825308665001712c75288510829510828110829115828510729514828525728515728510722681359115828515728510728560728515720726838513822c75288515722c80288510728560728510722c80282c65188120828515728514728513825304668513828515728510722c80188515725308662c80288110825308668515728513828510728110828110822c7528c3271a8515728110822c65188513822c75282c75188515728523828515728510728110828523728515728510728515728515722c8028911382852572851382851572851382c3271a8523728513822c74280605830605438513828523828513828513720607838515728513825081712c80288524728513822c7428951482851572851072530866852072851572851572851382851382851572851572852372851572851072c3271a851572c3271a851072811382811082c3271a9115828515728510722c80282c80188515728510728515728513820c28748515720721438515725308668513828510728515722c7528911582851382c3271a9115828515728513828513828515728515722c65188525825308668515728513728510725001712c80188510728525828510728515728513828510728515728513825308668520720605838515728513828515728510729513828510728525720605838560728515728513828510728524728523828515728510728514728513822c8028
    | 3 => 0x9513828515722c75288513828515728513825308662c8028c3271a911582852472851572851472911582240131c3281a8513828510728515728515725308662c75282c7428c3271a852372851572851072530866852572851072851072851382851382851572851572851382c3261ac3271a8510728524828523728515722c80282c74281681055308662c75288513828110820605838515728513822c65188513829115828515728510728515722c84289115828520728513825308668515728510728515728510729115822c75282c75288110825308662c75288515728523728515728510722c7528851572851072530866851572530866851572851382811082530866851572851382c3271a85157285138291158285257285138286084a8510722c7528c3271a8513822c7428c3271a8515728513828510728515728513828520728510728515728513822c80188515728510728513828510728110822c75288515720737838515728510728565729113828515728510722c8028178105851572851572851572851572530866c3261a852072852382851572530866851072811082168105856072851572951482851572851382c3281a8525728515728510728110828515722c80189514828515728510725308668510728120828510728510728513828520728515728110828515728513825308662c75288515722401318515729115828525728515728513828523728515728513828515728515725308668513822c65188515728510728110828513822c80288524728513828110828515728515828515728513828123825a04662c84282c74288110828515728513825308669514828515722c74288510728514828510729514828514728110825308668513825338668513828515728513828513828515728515728510728515728520728510725308668515728510728515728510728510722c80288515728514822c7528851382c25728851072851072851072c3281a8523728515728515728513728510720605838560728510725308662c80288515722c74288520729115828523728513828515728110828560728515728510728513822c7528851572530866c258288510722c75288515728513828513828513728510725081718515820c28748520728510728515728510728515728513828523828513828510728520728510725308669513828515728523728515728510728513822c75288514828513829110828565722c80282c7428852472530866851572c3281a851382851572851572c3271a8515728513828515828515729115828510728510723481308513828510728515722c75288515728510722c75288515728513828523728520728513828515725308662c8028852072851382851572530866060583c3261a8515722402312c7428912582911582852372851072c3271a4354302c75285304669113828513828515728510728515725308668515728510728515828515728515728513822c75288515728513829513828513828510729115828513828510722c80188520728515722c7528851572851072168105c3271a5308662c7428851082851072851572911582851382c3271ac3261a9115828520729115828515728510728110822c75288515728513829120828510725001712c75282c80282c75288523729113828513825308668513828510728560728515722c75189115822c80288513828110828515728513822c75288520728515728513828515729115828525728513828510828510728515728510722c80282c74288520728515728515725308665081712c74288515728523728515722651358515725308668515728513825308668515728510722c70288515728513829115828523728510722c73288515725308668513828510728515722c7528c3271a8510722c75285001712c75288515725081712c7428851572851072167105c3261a8515728513828515722c7528851072c3271a8560728523720605838513828113828515728510729115828510728510720605838515728514828513822c75282c70288510728515721902828520729515828513822c70288515722c8028811082c25728851382851072852072851072
    | 4 => 0x8510722c7428852372851572811082c3271ac3271a8510722c75288510721671058515728513828510728515722c75288520728510722c7528c3281a9115828515728513828510728515728515728510725308668113828515728510720721438515722c75288513828525728513828510725308669115828525728515722c7428851572851572530866c3271a851382851072851572851072c3271a8515722c6518851572851382851072851572c3281a85157285108285107285157285157286074a8515728515722c80282c73288515722c7528c3271a8523728515722c75288515728510728110825304165308668513729115828515728120822c80282c7528911582851572851382c3271a8110825308668515720735438513828515728513822a7428811082851072856072851382851072951482852072851572851372c3371a8515728520728510728523728515728113829115828515728513820605438515728513822c65188513825308668515728514822c74288515728525728513828515725308662c70289514828515728514729115822c75288510728515722c80281671059113828515722c75288513820735832c80280621438513825308662c7528c3271ac3261a8515728515728510725308665081710735438515728113822c75288513828510728515728513828510729115825a0466060583851072851072240131852572851072851072952482852372c3271a8515722c80189115828520728513822c84188513828515728515722c75288510728515728513825308668515728523728515722c8018851572851072c3271a851572c3261a8510722c7028240131851372c3271a851572c3271a53086685157291158286074a8520722681352c84282c75288520728510721751059115828514828514728510825308662c74289515828560728515725081712c80288515728513828515728513828110822c74289115828513828523828113822c75288515728510729125828515722c75288515728513822c75288515728510728515728513828510722c74288513828525728514828515725001718514728510722c80282c73288513828510728513828510728110828515728513822c74288513828515728510728113828510722c74288510728513828510728513828515728513828510728510822c80288515728513828510728513825308669514828513828514728510728510725308668513828510728515728510720621438513822c80282c75289110828515828515725308668513828513728510828510729515828513828515728510728513822c801885107285157281208286064a8515729115828513825941822c80280605838513828510728525728510729514828513828510728110829115829113828515728513828510725308668515728513828510724350308524728513822c75282c80288515722c752885157285138285157285138285138253086685107286084a5308668520728515722c75288515721671059120828515728110829514828510722c8028c3271a2c84288515828515728510728515728510722c75288515728515728513822c80282c8028851372851572c3271a8515725308668515720735838510728523722c7428851572851382852072851572851382851072851382c3261a9115820721439115828515728513822c75288510722c8028851572851072c3261a911582852472851572c3271a8515728515828513828513822c80288514728513828513820c28748510722c80288523728515728525728515728510729514829125828523822c7528c3281a8523728515728513825308662c80280737838515728513828513828515728523728515728513828513822c8028911082911582911582851572851482851072530866c3261a8525728515728510722c7528851572811382851572851382851382851572530866c3271a8515728513828510728513828515722c74288515728515728513829115828520728515728510722651358515725308668515728513828520728515722c7528072143851572851382c3271a851382851572851072851572530866c3261ac25728851572851382851072
    | 5 => 0x8515728513828510729115828515728510725941829115825308662c65188513828513728510728515728515728510722c75188513828515728520728515722c7028851382530866811082c3371a8524728515728510725308668110828515722c75289115822c75288520728513828513822c75288515728510725308669515828515729115828510728513728510728513828510721681058510728514828513825304162c74288520728513828510728110828510728515728513829115828513825308669513828524725081718513828510722c8028856072851572851082c3271a911082851382911582852072851572851382c3271a8513828515728510728515728513828110828515728513822c7428c3271a8525728510728525729123828520728510720621438515728513828510728515729115828525828515728513828523728515722c752885157281138285157285138285157285138286074a8513828510728515722c7528060583851572852072851382851072851382851072060583c3281a851572851382851382851072852382851572851382851072c3271a8515728113828515728513822c80288515722c75289115828515728515728513828510728515728510722c73288515722c8028851382530866072143851572851072852372851572851382851082851382851382530866167105851382060783060583c3261a9115828513825308668520728510728515728513828510722c7528268135c3271a851572c3281ac3271a86084b852572264135851572530866060783851572851382851382851072c3281a8523728515728513828515828515728513825308668510728510728513829514828523728110825081719115828515722c85288515728513728510728110822c75188515728513828510722c80288514725308662c75288515728510728510722c80188510728510722c60282681358515728513722c75288513822c80288513828510728510721771058514828513828510822c7528c3281a5308662c75289514828513828513822c8418c3271a8515728513829115828515728560728515728515728510725308668515728513825308662c74289514828513822c75289110828515725308668513828510725308669115828515722c7428168205c3261a8515728514728513825308668525720621438515828515722c80288515722c80182c75280605838510725308668510729514828515728513828510724350302c75288510728515728510725308668513822681353481302c8028851572851072530866851572c3261a8515725308662c80182681358510728520728513728515728515725325665308668510725308668565728510729125829514828513822681358515728510728510728523728513828113820721438515728513825308662c752824013107214395138294274c851572530866c3271a8513822c8018911582851572851572851382c3271a2c80288515728510722c75288515728510728110825308668515720721438515728510729115828510728515722c7528240131c3271a851572851072060583c3271a8513828513728515728513825308660721438515728513828515728515728510828510728523722c75288513822c7528951482851572851072508671c3261a8510728520728515728513828515728510728513828515728513822c75288515728513828510722c74288513828510728513822c6518530866851572951582851572851072851572851572c3281a8513828110822c7528240131851572c3271a96084b8515728513828523728515728110825941828515728510728515728513828515722c7528c3271a8513828510728513828510728515728510728515728513828510728510729165822401318513825308668515728510728520728515728515728513828513725304668510728113828515722c75282c75282c74288513828510728515722c70288513828513822c7528851072851572c3261a912582911582851382530866851572851572851072851072851572c3281a8515728523828515728110822c8018852572851382851082852572851072851472811082
    | 6 => 0x8510722c752885138253086686074a8513828510728113822c75288515722c8018851572851382851572851072852572851072851472851382c3261a8560728513828523828515728524728523728515728513822c74280605835308668510725308668523728510725308668510728523828515722c7528951482852382851572851072c3261a8515728515728513822c8028851572b4270c852372851382851072811082851382851072811082851582851072851382851072851572911582851572851382851072851382851072c3371a811082851472851572851382851572911582530866851572851382c3271a8513825308662c8028c3261a2c75288515728513828510728513822c802885157285107285157286074a8520728513828515722c80188523728515728510728520728515728523728510722c80288523728513822c7518851572851072811082851572c3271a2c75288565728515728510729515828515728515728525728515728513828510722c75288513828510722c70288513828515728513822c73289113828515728513828513828510828510725941822c75289115828524728510728515722651358110822c7528508171851382851072530866c3261a951582851572851382240131851572508171c3271a2c75288515728514828510728513825308662c73288510728515722c7528852072c3271a851472851382851072530866c3271a8513828510722c80288520728515728515729513828515728513822c8028c3271a
    | _ => 0
  (block >>> (24*(i % 512))) &&& 16777215

def roff9 (i : Nat) : Nat :=
  let block := match i / 512 with
    | 0 => 0x38538438238037e37c37b37837737737537337036c36836736636436236236035f35d35c35935835635535235234f34f34d34a34834634434434234033f33c33a33633533533533333133032c32b32932732432231f31f31d31b31b31831831731631431231030e30d30b30a3083073053012fe2fc2fa2f82f42f32ed2ec2ec2e92e72e62e42e32e02de2de2dd2dc2db2db2da2d72d62d32d02cf2cc2cb2ca2c82c62c62c62c52c32c22c12bf2be2bd2bc2bc2ba2b82b62b32b02af2ae2ad2a92a82a82a72a52a42a22a129f29c29a29a29829829729729529028e28c28a28628027f27d27927927627627527427227127027026f26d26c26a26826726326025e25c25b25925725625425024e24c24924724724624424224023e23c23c23b23823723523323222f22b22922822722522422322121f21f21b21721421421421321020e20b2092072062062052032032032031fd1fd1fc1f91f61f51f51f31f21ee1eb1e81e51e31e21e21e01df1db1da1d71d71d51d31d11d11d01ce1c91c71c51c51c51c21c01c01be1be1bd1ba1b61b31b21b01ad1ad1aa1a71a41a41a31a119d19919819519419018f18d18a18818718618518418217e17d17b17917817617517317016a16516416216116116015e15b15a15a15815715515415315014d14d14b14914714414214114013f13e13b13a13913913513413213112f12e12e12c12a12912812512412411e11d11b11911811711511411311110e10b10a10a10a1081071061010ff0fe0fb0fa0f80f60f50f30f10ed0ea0ea0e90e70e60e20df0de0dd0dc0d90d60d30d00cc0cb0cb0ca0c80c80c70c70c60c40c20c10bd0bd0b90b70b70b50b30b00af0af0aa0a70a40a40a30a30a109e09d09c09c09b09909809709609409208e08e08c08b08608407f07c07b07807807507407307207006e06e06d06d06b06a06906806406406105f05e05d05a05905905705705505405405104f04e04d04b04904504103e03d03a03703303103002e02d02b02802702502402302001f01e01c01c01a01701601501401401101000d008006005005003002000
    | 1 => 0x71771471371171070f70c7087067057047047037037027016fe6fc6fc6fc6fa6f96f76f56f26f06ec6ea6e86e66e46e26e16de6dc6db6d96d76d66d66d56d16d16cf6cf6ce6cc6cb6ca6c76c76c56c56c36c16c16bf6bf6bd6ba6ba6b86b56b26b16b06ad6aa6a96a66a56a26a26a26a169f69d69b69a69969769469269068f68b68b68868568268168067f67e67d67b67967467367267167166e66c66b66866666366266165f65c65965865364f64d64b64964864664564464364364063d63b63763563363163163062f62e62c62a62962662562362162162061c61a61861661661460f60e60c60b6086066056025ff5fc5fa5f95f95f95f85f85f65f45f35f25ef5ef5ed5ec5eb5ea5e75e55e45e35e15de5dd5d95d85d75d45d15cd5cb5ca5ca5c95c85c55c35c35c25c15bf5be5bc5ba5b95b75b35b05af5ad5ab5a95a85a65a45a35a259d59a59959859759759559359158e58c58958658558558258157e57957857857557357257056d56d56a56956856656456456256255f55c55a55655555355054e54e54d54b54a54754454354054053d53953853753753653453253052f52e52a52652352252151f51e51c51c51a51851651251050e50c50c50c50b5095095095085065055035015004fd4fd4fa4f74f34f34f24ee4ee4ec4e94e84e84e74e54e44e24e04de4dd4dc4db4d94d54d24d14d14d04ce4cb4c94c74c64c54c34c24c14bf4bd4bc4ba4ba4b74b44b34b34b24b14b14af4ac4ab4a94a74a249f49c49a49949849749349248f48e48d48d48a48748548147f47f47d47b47947847747347046f46f46d46a46846346346246145d45945745645345345245044e44e44d44c44c44b44944844844644243c43a43743543443443343142f42d42d42b42a42942842742542542341e41d41b41841541341241141140f40d40d40d40b4074054034003fe3fb3f93f73f53f23f13f03ee3ed3eb3ea3e93e63e43e03df3db3d93d83d83d73d73d53d33d13cf3cd3cc3c83c63c33c23bf3bc3bc3bc3b83b63b23b13b03ac3aa3a73a53a43a33a139f39d39a39739438f38d38a388386
    | 2 => 0xa9da9aa98a97a96a94a91a8ea8da8ba89a87a87a85a84a83a82a80a7da79a77a77a76a75a73a71a71a6fa6da6ba69a69a69a66a64a64a63a60a5da5ca5aa58a57a56a53a52a51a4ea4ca4ba47a43a41a3fa3da3da3aa3aa38a36a33a32a30a2ea2da2ca2aa26a26a24a22a20a1fa1ea1ca1ba19a18a18a17a12a12a11a0fa0ea0da0ba07a04a04a02a009fe9fc9fc9fb9fa9fa9f89f79f79f69f69f59f29f09ed9e89e79e49e39e39e09df9de9dd9d99d59d49d29cf9cd9ca9c99c79c69c29c19c09be9bb9b99b69b69b69b59b19b09af9aa9a99a79a79a49a29a19a099f99e99d99c99b99999899599399399399198e98a98998898798798598298198197f97c97997797697597597397096e96c96996996696195e95d95c95995795695595495395195094e94d94b94894794694594494394293f93e93b93993793393293193093092e92e92d92992792492192091e91991891791791391391190e90d90c9099069049008ff8fd8fb8f78f78f78f58f28ef8ee8eb8e98e88e68e58e28e28e18e08e08e08dd8db8d98d78d58d48d38d08cd8c98c58c38c18bf8be8be8bc8ba8b88b68b68b58b58b38b18ad8a78a58a38a089f89d89b89a89989789789789689489188f88c88b88988788488188087d87d87c87b87a87a87a87887787587487287086c86b86886686486286085c85a85a85885885685485285084e84b84784684184083e83d83c83c83983883783683583183082b82a82a82982882782682482081f81d81c81b81a81681581381381180d80b8098078078058028007fd7fc7f87f77f77f77f67f47f37f17ee7ee7ed7ec7e97e47e27e17e07df7de7de7dc7db7d97d37d17ce7cd7cb7ca7c77c57c17bf7bd7bb7ba7b77b77b67b27b27b17af7ad7ad7a97a77a67a47a17a17a079e79b79779579379078e78a78878678578077f77e77d77b77977977777677377176f76e76e76976776376176075f75e75c75b75775575475074e74e74e74d74c74a74874574374073f73e73b73873773473273273173073073072e72d72c72a72872772572572472372372172071d71b71a719
    | 3 => 0xcbccbacb8cb3cb1cb1cafcadcabca9ca6ca4c9ec9dc9dc9bc98c97c94c92c90c8fc8ec8bc8ac85c82c81c80c7ec7dc79c79c77c75c74c72c71c6fc6ec6dc69c67c64c62c60c60c5fc5fc5cc5ac57c55c52c50c4fc4cc4bc49c49c49c47c46c44c43c3ec3bc3ac37c34c33c2fc2cc2ac28c27c26c26c24c1fc1ec1ec1dc1bc1ac19c19c18c16c15c14c14c12c11c0cc0ac08c06c05c05c01bfdbfcbfcbfcbf9bf8bf6bf3bf3bf2befbeebedbeabe8be8be7be2be1bdfbdfbddbdbbd9bd6bd4bd2bd2bd0bcdbccbc8bc6bc5bc5bc4bc3bc1bbebbbbb8bb6bb5bb2bb2baebacbabbaabaaba9ba7ba4ba4ba4ba1ba0ba0b9cb99b98b97b94b91b8fb8eb8db8bb88b88b85b84b81b7fb7eb7db7bb79b77b75b72b71b71b6fb6db6bb68b66b65b63b60b5fb5fb5fb5fb5eb5cb5ab5ab59b58b58b56b55b53b52b4fb4fb4fb4db4db4bb49b48b46b41b41b40b3eb3cb3bb3ab36b32b31b30b2fb2bb28b26b23b1fb1cb1ab18b17b14b11b0fb0fb0fb0db0bb07b04b02b02b00afdafbaf9af6af2aefaecae9ae9ae5ae0ae0ae0adeadbad7ad5ad4ad1aceacdacaac8ac6ac3ac2ac1abdabcabaab9ab6ab4ab4ab2ab1ab0ab0aaeaacaacaacaabaa7aa1
    | _ => 0
  (block >>> (12*(i % 512))) &&& 4095

def code8 (i : Nat) : Nat :=
  let block := match i / 512 with
    | 0 => 0xa3ea58b4d025e0dfae2d33572a27eb82ab51c689fae252d471a2fa18b4b51d28de861cab474a2bf882bb51c60dfae06c5514c37ab70a251ca0f79e1ee9421e1da757a850860fe861ef4892a39e7874a508685fbe06ab424a3da787a850870bb95da89471c3f2370b3d0930f39d4ace821a35e7874ad08687ee025ef494a1dd8f9b9d0528de861eeb494a2fad81b851d28beb606a1472a37a187bad0870b79d5ace81483fa18ba3a0530afb5d289421c3ce772b3d0528fa4e4861421e32d255aa50868fa8626a5474a36e581bad0868d79e06eb424a36e587bad2528dead1d21474c27ed75a250860dfae2d25471a37ab874850870f69d42c3474a37ab82a851d28bdb60ae3474a3ea581b851ca8be861d2d421c1de777b150528bdb626e3474a39f88b79d1d287b962d2f421a27ed81bad0868beb50861421a3d638b29d0520fd8e2d2f414a3bb8097a50868eea606a1472c2ee576a0d1d38d69d56a1474837eb8baba0860bfb62e8e824a3db80b79d0868afb61c69421a2ded8b29d1d30b79d5ac9421c39e774b50c928d79e086b424a376387bad1d289fb61c6b421a3d674748d1d28beb61ea1421c2de756b151d30fa4942d4571a36e587bad1d20dfae1ec5514c1faf70b150538c79d56a9421a3d6782a8d1d28779e2d2f421a3db80979d0870779d5ec5414e0de757ab50860f765e5e7474c2fad50b251c68b79e1ead421a37a187aad0920dfae2ac4814a3ea58b1d025e83fbe0aed421a2bed874a508685fbe086b42482fed8baba08689fb61d2b421c2de776b3d0870f69dc2cf41483fa187ba508685fbe2c6b494a17ef81bad1d384fbd56a9421a2f6d8718d1d20fe862ace221a1fb809bbd0860dfae26c5514837eb8bab90520dfae2d2f421a27eb874b50868bbb626a547482fed82b8d1d20fb9612cf514a3ce78b1951d28db9606ab474c27ed75b3d0528f39e26a547482fed89b3d4500ff65e6a281483f9590b10c5309fb5d6c5414c3d6771a0d1d30beb542c3474a2fad81a851d20f79e2d2f414a376b89b8d1d30d79d56cf421a2ee58b4b51d389eb556a1474a2f7822bb508689fae2d2d421e15e757aad0868b7b626a747483de784b3d4528eea606e1472e3e2551a851d285fbe06eb421a37b801bad0868fa962d2147283de78b4bd08687e862caf42182fed8bab88930fc8dc289472a2f6d4748d1d283fb62d2f421c33eb74b3d0860f79e2e8e824c17ef75a250860f79e2eae41483de78b48d1ca0fede1d2142182fed8ab120520dfae26d4972a36d3921ad0878b59d5aa3474c1de757b108520fe861ee541482fed87b5248705fbd56cf421c2f6d71b3d4528be860aad471a1faf81b851ca0fe862eae821a1faf8b4d025e0dfde252b474a27ed81bad1d20bfb606cf514c2de756b3d0530f69de814897a3f2382a851d28fa962d2142183fa18bab90520f79e2c65414c3eb412b5225e8cfe225eb494c3ce772a0d1d28cfa61eeb474a39e7421a50870b79d5ace27483de78ba3a0528f3e12de7414a35e7421ad0868cfe206eb424c27ed75b4d1d20dfae26cf514c2ee576b3d0530d79dd6d3474e366551aad1d20bfb62c65474a3ea5474851d287ebe2c74097c36e575b4d1d28d7e2a6e7474a2bf882bb51d289fb60aab474a35eb89a9d1d28cfa61eab421a37a1872ad0920bfb612cf514c27ed75b3d0928b79e26ad474a3da78b4851ca87763e6e7474a1bef421a50878f29d4aa1474a2de7474b51d285fbd086b421a27ed81bad09305fbdd6c5414a2fad8b4d025e0bfde1d2d421a2f7822bb51d28b79e0aad474c3d6751b3a0878b69d5aa1421a2de782bb51c68dd8e0aab474a37ab8b4850870b79dda89471a37a1874ad0928beb606e1472a37a1821ad0928ddae0ae3474a27f8a2bb50868deae06a1474a3f2189b8d1d207fbe2ac4814e33ab50aa50868fc860aa347483fb7872851d30beb5c2cf424c2fad70b3d0528db951d2b474a1f638b4bd08783ebd5aa1421a35e781aad0930db9556c5474c35e755b250868b7b62ca7414a39f88b79d0868bb961d2d421c2de776a0d1d20efa62c65414e34e752aad1d28d7e2ade7421c3da770a250868deae2521472a27eb89ab51d30bdb5c683474a39e98b29d0528d79e1eeb47482fed87ba50868de8606ab424c0fef76b150530f69d42cf421a2fa1872b508789db546ab474e2ea556a851d28d79e0aab474c17ef55b250870d79dd6cf42483de781b154530d79d56cf414c3ba174b3d0868eea606e1421c3da750b3a053c69b95c64914c3da750b108528eea606e1474a37ab87a850868d7e2ade7414837eb82b8d1d289fb6086b424a37ab894851d30beb5c2d3474a37ab894850860fe8626cf514a3da18b29d1d20efa61ec5514c1faf50b3d0860fe862caf414c3da770b4d1d28dee025eb474c3ea550b151d30f69dc2c5414a17eb8b4bd0870db95d6cf414e23ed55aa50868fa9606a1474a3da78b4851d20fe861ec5514a3da189a9d1d28f59e26e3474a2fb8097b508607fbe06c5514a2f638b4b51c60f75e4eae421e34d253aad0868dd8e1eeb494a3e6589b8d1d30f69d42c5474c2f6d71b3d0920fee02df3414a2fb802bb51c68b7e32de7421c2ee556b0d1d28779e1d2f421c35e775b3d0870b79dda89421a0fef8b4b51c60f79e1ed492182fd596b38c930f69dc2cf424c3da750b1505389b955aab474a33f881bad0868d7e2a6e7421a36eb8b1951d28fa862c65474c2de756b388860fe861ed4324e1ad257aa508685fbe06eb424a3db80b79d0520df65dc6b424a27eb82ab51d30b79d5ac3474c0fef56b2508785b495eab421a3ba1874a50868d7ae2527414a33eb87ba50870d79d56ce814c2fad50b250868d7ae2ca7414a2be982ab51c60df65dc6b421a37a1874ad0868b79e2d2d471a37ab421850870b79d5ac4214a27eb87ab508689fb61eeb494c2fad70a251ca89fae252d421a0fef8b4b51d283fb61c6f421c2de756b3a0870deadc2cf414c37ab70b4d1d309fb5d6cf42183de78b1951d30b79ddad347483de789b3d4538679d5ea9421a3cf84b79d1d30f99546c547483fa189b3d4928e79e1ea9421c2ee576b4d1d20fb9626cf514837eb8b4d125e8be8626ad474a35e787bad08689fb61eab424c3ce772b4d1d28d79e1eab421c376355b0d1d28f58e2ca7421c1bef74a250868be860aad474a3f23474851d28f39626a7474a2fad82a851d2877be2ca7421a3f23874850870dead42c9421a3d782b79d05283fb61d2f421a1fa18b4bd08689fae2d2d474a33eb874a50878f49d46a1474a3f238b4851d28b7b62ca7421c3d6771b3d0928bee00aed47483f9590b394528fa6165e1421a3d6782b8d1d28afb50869421c1de757b250868dd8e1eab42483f995b04bc528deae06e1421a3ea1872951d289fb5086b421837d9771ad1d28afb61ee942183de79ab3a0868cfa61eeb421a2bed87aa50868fc860ae3474a2de78b4b50870deadc289421a27ed87bad1d28de8606ab474a2de782bb508689fb61eab421a33e987bad2520dfae2eb251483fa187b952528db961d2b424e2e9256a850868b7e32de7414c3ea570b3d0530f69dc289472a39e98b29d1d30db9556c3474c2de756b3d0868d79e2c6b494a2fb809bb51c68ddae2523474a3763474ad1d28fa961d21421a27ed87bad0928beb626a1474a376b82a8d1d20fe8612cf514a35eb8b29d1d20fe862d2f421837eb87ba50868bd8e1d2d421837eb87b524868b7e32de7474c35e755b0d1d38d59d46ab474a37b801bad1d28bb9626ad474a3da7474851d28d79e1eab424c37ab70b150528f69e1d2142182fed87b8d1d30e79d52cf42183de782b8d1d38bcb546a1474a3da782a851d30f69dc2cf42182fd596b3a4928779d086f421c2fad70a250868deae2c74097e369255a850860fe860ae347483de78ab3888709fb556c9421a37b8097ad0928beb62d21472c1bef54b3d0860f75e4eae414c3ce752b3a0528f5e0ade7474c33eb74b15452877be2ca7414a2fa1872b51d28beb61c61474c2de776b150528dbae2525474a2fad871850868be861ead421a27ed89aad1d20dfae12cf51482fed87b154530f69d42ce414a35e789aad1d28deae06a1472837eb8ba3a0928f69e06a1474e39a750aa50868fa9606e147482fed81b154528db9626ab474a37ab81b851cb0beb5c2cf421837eb87b50c928d7ae2527474a37ab89a851d28d79d1d2b474e35a755a850868dbae2d25474a2fad8b4851d30beb5c2c5414837d595b4a5c70d79d56c5474a27ed87bad08709fb556c347482fed8ab388868b79e1d2d421c35e755b120520fe8626cf521a2fad474851d20f79e2eae224a36e58b1ad2528b79e0aad471a2fad874850868de861eeb474a35e781bad08786ebd42a9421a3e985948508689fe28aed47183dd97979d0878b69d5aa1474e26d256aad0868f6e025e7414a27f8a2bb51d385ebd56a1421a3ba98b1d025e8f3e12de7421
    | 1 => 0x28dee025eb494a36e5874ad0868b79e0aed474a27ed871ad1d28deae2d2147283fa18ba3a0930fa95c2d3474837eb8bab889289fb62c6b49483dd793ab91d28ee861ca9421a3f238b4850860f79e1ed4324837eb82ba51c68d79e06ab474a2bf882bb50868de861cab42183f9590b3a4528f6e02de7474a3da781b851d28bde08aed471a2de78b4b51d30fa9542c3474e29e756aa50868af6266ed47482fd9794b50860f79e06e9472837f7874ad08707ebdc28942182fed8ba3a0520bfde1c6d421e25e756aad0878da9556a1474a33e9821ad0928beb62c74097c3da750b3908689fae252d474a27ed474ad1d28db961eeb424837eb8b1951d20fe862c65474a3da78b4d025e89fae2d2d471a3e654748d1d30bb955ac5474a37ab8b4851d28f69e2d21421a1faf8b4850868ee850869421837f7894ad0928f59e2d23474e25e756aad1d28e7a62ca7421a1faf81b8508782fbd5aa942182fed87b8d0920dfde086b424a33eb894a51ca8dee025eb421e3c6752a8d1d20fe862eae224a35e787bad2528fc861ca3474e07ef56aad0870f39d4acf414e1cd253abd08687e861caf421a33e987bad0920bfb62eae414c39e774a250870f69d42ce821a3da7421850868bee00aed421c35e775a250868fa962d21474c2de776b3d0920bfb62c6f424a3ea581b850868dd8e1d2b42483f6387b154528eea61ea1421c3ba174a250868dd8e1eeb421c0fef76a250870f59d46c5474a376387bad0930b79ddacf414c39e754b1085283fbe0aed471a1fa1874bd08683fbe2d2d421a3da781b850868cfae1ea9421a3f380978d1d28deae06e147483de78baba08687ebd0861421a36d8594ad0868beb62d21421c35e755b108520bf65e52d471a33eb89ba50868d7e2ade7474a37ab8b4d025e8d79e06eb474a3da18b29d0528fc8e2d34097c3da750b250868bd8e2d2d421a2fb809bb51d287ebe2d21472c39e774b3d0868bb962d2d421c1de777a250868f39d1d2547483fa182b3d4930f69d42cf41482fd9794b51d28d7ae2527421c35e755b3a0868fc8e2d21472a0fef82bb51d38b9955aa3474a39f88b79d0530f39dca85474c1de777a3d0860bfb61ed432482fd596b10c930f69d42ce474a2de7421b50860f765e5e7414c1faf50b250868de861eab494a37a189aad1d30f59d46ce814837eb84b154530d79dd6c5414a37a182aad1d287ebe2d21474a2be987ab50860dfae2e8e814a17eb894bd0860fee02df3524a17eb874bd0870deadc2cf424a3eb8097951d20fee02df3421a33eb421a50868d79e1d2b42483fa181b154528f69e26a1474a2eed871951d28e79e1ee9421c2fb416b5225e0fee026ef414a36e587bad0868dee006eb424c3e6571a0d1d30afb5d2cf421a0fef421b50868fa9626a1474a2f6382ab51d28d7ae2ca7421a1fb8097bd09289fb606ab474a36e581bad0928f6e025e7474a2fa1872b51c68f5e0ade7421a27ed81aad0930d79d56c5414a1def8b29d1d303fbd5acf42183de78ab120528dbae26a5474a3da18b29d0878ea4942a9421a2fa18b4b51c68bbb62c65474a1faf81b851d30db4956c551483fb7872850868f69e2c74097a2ee5474b51d20bfb62d2f42183fb9697850868bb962d2d471c37ab70b3d08689fb61c6b424e2bad50aa50868ed8e1ee942183fa18ab1205309fb556c9471e2ce752ab51d28dd8e1d2b421e27ad55a850860f7e54ec5414e3c9253a850868f58e2ca7474837eb8ab3888689fb61eab494a2fb8097b51c60dfadee92814a3da781b851cb0d79dd6cf414837eb8b4bd24a8d79e1eab494a36d8597ad0868be862d2d421a36e587aad2530fc8d42c347483ed9772950528dee02c6b49483fa187b524870dd8dd6cf424a27ed874ad0928beb606e1421c33eb74a250870ded056d4897a2f638b4b51d283fb62c6f421837f7874ad09387a495ea1421e372355a851d30b79d5ac5414c3ce752b0d1d28db9606eb474a3da781a851cb0fa95c2cf524a2fb8097b51d28ee861ee942183de787b154538ab495aa9421a2f6d82a8d1d28de861eeb424a33f88b1ad2528bee026ed421a33f881bad1d28ee861ea9421a35e787bad0928af6266ed471a35f8a9b9d0528de861eab421a3ae587ba50870b79d5ace214
    | _ => 0
  (block >>> (50*(i % 512))) &&& 1125899906842623

def offset8 (i : Nat) : Nat :=
  let block := match i / 512 with
    | 0 => 0xbd6f5bcef1bbeedbaaeaba2e3b86dfb76d8b5ed5b4ed1b3accb2ac9b12c4b02bcaf2b8ad2b3ac2afabaadaaea9aa2a8a96a5a92a3a8ea1a7698a5291a3a8ea3a8ba2688a1e83a0a80a027d9e6769d6739ca719ba6d9b26c9a2689925f972589565294a5293e4a91e4691644912418fe3c8f2388d6358d2308b62d8b6298a22689a2488e218761b85e1485212846108360a81605812007f5fd7f5fa7e1f67d5f27c5ef7b5eb7a5e8795e3785de76dd975dd674dcc719c4709c06f9bc6edb86ddb66d1b26c5b06b1ac6a1a769da6691a36819e66d99659936398a6298a62183605805f5795d9745cd725bd6d5a96859d665916358d6257d5b5695a55d5554d525414e5354b52d49511404fd3d4ed3a4e9384d9354d1334c9304b52d4ad2949d2649525491234891f46d1b4651845914445104350c425074150441102401003f4fb3e0f63d4f03b8ea3a0e7390e0378dd36cd9358d3348d2334cb318c3308bf2f4ba2e0b52ccb22c4b02bcac2b0aa2a0a7290a22809e268982589524c8d2308b22c892148420c801f87c1e8781e0751c8711b86c1b06b1a86a19c6418c5f1745a15c56154511404d1304a12448114451144410c3f0f83d0f03c0e4370d8330c4300b42c0a427094210741a05c17050130400d0340b028080180200800
    | _ => 0
  (block >>> (10*(i % 512))) &&& 1023

def proof8 (i : Nat) : Nat :=
  let block := match i / 512 with
    | 0 => 0x851572851072852072851072852072851572851072851072851072951382851472851072852072851482851072856472c3271a8514828510728514728510720621438515728514822c84282c6528c3271a8520728510728514828510722c64288510720605438514828510728515728514728510728560728510728515728514728514822c84288115828523728515728510728510728523728510721681058510728510820605438510728514728510728514822c84280621438515728510722c742896064a8514728510722c84282c65188514822c84288514828514728510728510728514728510728510728564828514828514728510728560728515728514722c84288520728510728515728514728510728515720605838510728524728515728515728510728515728510722c85288514828514728510728514828510728514722c65188515728514828510722c8428062143c3081a8515728514828514822c84282c65188514822c84288520728510728515828515728510728510722c60288524722401318510725308660605438520728514828510728510728515728514828510722c84282c65180621438524720605838510722c84282c6518c3081a8515728510722c84280607438520728515728510722c84288515728510728514828510722c8428c3261a8514828510728510729525828520728510728520728515728514828510820621438524828510728514829125828525828514728510722c84280605838510722c84288514828510728514828510722c8428c3081a2c8428851072851472852072851582851072851572851482851082851072c3081a9525828514728510728115828524828510728525728520728515828514728510728524728510728514828510722c84289514828510720605838510728524728515828523728510728120826c625a8520728514828514728510728514728510728520728515828520728510828510722c7428851582851572851072852472851572c3261a851582851072c3081a851572851482851072851482851472851072811582c3071a8514728510722c84188515828510728515728514828510722c8428851072851482851072c3081a8514825308668560728515722c84288510728515728514728510728115822c84288510728515828515728510728525728520728515828515728510722c842885107285107285147285107285107204260c6053438510728510728514728510722c84288510722c84189515728510722c84188510722c84288515828510725308168524828510722c84282c84288510728515728510728510728115828514829115828515722c84282c6518c3261a8510721681058514728510728514728115822c84288515728514820626838514729524822c84288515828560728524820605438515728510728510722c8428851482851072c3081a8510728120828520728515728524728510728510722c8428c3271a8515728514828510728510722c65182c842885148285107285248269804b8510722c65188564828515728510728510722c84280605839725828510728510728520728515722c84289514828514828510722c84282c64288510728115822c84288510728510728524728514828510728524828514828510728524728510728524828514728510728510722c6528c3271a8510722c84282c80288510725308662c6428852472851572852472851572851472851072852472852072851482851072851572851482851072c3271a8510722c8428851572851072c3271a2c65182c85289514828520728514728510728515728524728510722c84288510722c8428c3261a851072c3081a851482851072851072060543852582852072851072852072851072851072951482851072c3271a8510728120822c63282c84288510728510722c84288514828520728510728514828514728110828510722c84280605838510728510728514828510722c8428851572851472851072851072062143851572851072c3271a8510720605438510728514828510728524728510728520728510728564828524728520728510728515722c84288514722c6518851072060583c3271a
    | 1 => 0x8510723481300605838514729524828510722c84288515828510728115822c84288510728510725308662c84288564828520728514828510720605438520728514728510722c84288520728514828510725941828510728510722c84280605838560728510828514828510728520728515722c84280605438510728520728510722c85288510722c84288510728514828514722c65188510728510728515828510720605838515728514828510728514822c84288510722c74288524728510728514729115820605831681058524728510722c84288510728514728510728514828510722c84288514728514828510728514728510722c6518c3081a8520728514822c8428852472852072851572851072852472504671c3271a0605838515728510728514728510720625438520728510728515728510728565728510722c84288514728510728520728510722c65188510722c64288515728510722c6518851072851572851072a4580c8515728514822c8428851072851472168105851472851572851072c3271a851482851572851482851082851072851572851472c3281a2c84288515828515728510728514728510722c84288515728510722c8428c3081a8524728510728520728514828510728510722c65188524728520728515828514822c84282681358564828510728520728515728514828514728510728524828510722c84288510728510728520728510722c65188514728510728520728515728514728510722c65188515728510720605432c84288510728524828510728514728510722c8428062143c3261a8564822c84298520728520728514728510728515728510728515828510728515728510728514828510728520728515828510729514828514822c84282c84180605838514728510728115828515728510722c84282c64288514828525828515728510722c84288510728515722c8428851072852072851082851072851572851072c3261a8514728510728514728510722c8428851482851072c3261a8510728510722c84288520722c8428851572851072852072851072070543851072851072c3081a8520728510722c84288520828515725308662c64288520728510728514828510728515728514828510728515828510722c84188564828525728524728510728510728560728514828510725086718510728515728564828520728525728520728513828510728515728510720605438515728510720621438514720626838515828515728510722c84288520728514822c84282c8428852072851572851482851072852472852072852072851572851072851472851072060583060543c3081a8520728510728515728510722c84282c74282c65188520725308668524728510728510728525828510722c8528856072851072851482851472851072851072240131852482c3261a851072c3261a8514728510728510728524728510729115828524828514828510720605438510728510722c65188515728510728525728510722c7428851072508171851072851482851072852072851472851072c3081a8524728514828514722c84288515728510720605438510728514822c65182c6518168105852072851072851072c3071a851482851072852072851072168105c3081a852472851572851072811582811582c3261a8510728115822c65188510728515828510720621439125828510728515728510728514828515728510728114828510728565822c84288524728510728520728510722c84182c65188514828510728560728515728510722c6518c3271a8510728520722c85280621438514828520728510728524728510728510722c84188510722c84288514828515828510728115828514828510722c8428851572851072c3081a8524728510729514828510728524828515728510728510728515728514728564828515728510728115828524828514828515828510728510728515728514828514728510728510728114828510720605838510728514828514828510728510728510728514828514728510728510728520728514828514728515722c84288514728510722c85280605438520728524828510728514720b0183
    | 2 => 0x8510722c84288515728510722a85288514828510728510728115822c8418c6265a0605438514828520728515828510728510728560728510728510729514828514828510722c84288514728510728510728510728510728514728510728524828520728514728515728510728524828514828514722a84282c84288514828514728510728515728514828510728515728510728520720605838514728510728115821681058520728515822c8428852072851072851072852472851472851072060583852072851072851482851572851482851072c3261a8514829514828510722c65188525728520728510722c65188510728510720621438510728510728510728514822c65188510722c84288520728514728510728514722c84182c6518851072c3261a8520722c8428c3271a8515728514822c85288510728515728515728514828510728515728510728514728510728514828510728514828510728520728515728510728564828515728510722c74188515729120828520728510722c8428852072851072851072851572851072851572851072851072c3271a8515728510728510722c84288514822c8428851072c3261a8514828520728510728510728515728510722c84282c65182c84288514828510728514728510728514822c65188515728514823401308514728510725308668524728514728510722c8428851572851472851072851482851072240131851572851482851072852072851072062143851572851072852072951572851072062543c3081a851072851572851572851472851072851072811082851572851482c3081a8510721681058514828515728514828510722c84288510728510728510728515728520728510720621439514828510728115828520728510728520728515728110828510728515728510722c84288524728520728510722c8528851572811582852072851072c3271a8514828510722c84282c6518851072530866851072851072c3081a8510728515728514728510722c84280605838520728515728510720621438515722c8428852072851072851572851572851072851482851472060543851072851072851482851072851572851072c3081a8510725941828514828510828510729524822c842885147285107269804b8515722c64288520728510722c84288515728514828510722c8428851072851572851072851072811582851472062143851072c3271a8564828560728515722c84288510728520728510728515728510722c84288510728515728510722c6518c3271a851072062143851572851072348130c3081a9514828510728520728510728564728510728510728524728514828515728510728515728510728520728515728510728560728524728515728510720605438514728510728520728510728510728510728524728510722c84188510728514828514722c84288510728510722c84288515728510728514728515728514828525728115828510722c84282c84188514828510728510728510722c8418c3271a8520728510728514728510728510728514728510728510722c85282c8428c3271a851072851472851072852472851072852482852472851072062143c3271a851072c3071a8510728514828510722c6428851072852472851072851582851072c3261a8515722c65188510728514828510722c64288510728514828510728525728510722c65188510722c84288520728515728514728514728510728514822c84180626438510722c6518851072951482852072168105c256188514728510729514828515828510728510728510728514728510726012438510728514822c84288514828510720621438514728510728510728524728510722c8418c3271a8510728510721681058515728514828510728520728510728514828514728515722c84288510722c84288510720621438510722c8428060583c3081a8514822c65188510722c74288520728514828115828520728515722c84288514828510728510728524728514728525728514828514728510728514722c8428852072852072851072851482851072851582851472811582175105851072852072851072851482
    | 3 => 0x8510722c84288514728510728510728515722c8428c3271a8515828515728510728515728510728510722401312c64280621438514728510728520728515728514728510722c8428851482164105852472851572851072851072852472851482851072851582851072851072851582851072811582852482851072851482851472851072852472851072c3271ac3261a8514828510722c65288510728514828510722c84288515728510728510728510728515722401319514828524728515728510722c84288510728524728514828510728514828520728515828510721681058510728515728514828514728510721681058514722c8428851072c256180621438515722c8428851072851072852482c3271a852482851572811482c3271a8524728514828510722c8428060583851472851072851572851072c3081a8510728510722c8428852072851582851372851072605043851572348130851572851072c3261a851072060543851072060583851072852472851072851572851572851072851072060583856582851572851072851582851482c3261a8515728514828510724358302c65188510728560728515728514728515728510728514728524728510728510722c8418851482851072851472851072851582851072851072851072851072852072852482851072851472c3271a8514728510728514728510721681052c84288510728515728510722c8428060583851572851472851072851472851072852072851072851572851572851072605243851072530866508171c3271a8510720605838515728510722c8428852072851072851572851572851472851072851572851072851572851072851482851072852482851472851472851072c3081a8520728510728514728510722c8428812082851482c3261a8515728514728510728515728514828510722c8418851072851482851072851072851572851072c3261a9125828524728515722c84188510728510728525728510728510728510728510729514828515728514828510728514728510728514728510728525728510729514828510728515728514828510728525728515728510722c84288520728514728510728525728510728515728514828510720605438514828514728524828515728510728520728510722c8418851072851572851482951482851072851072852472851072851582851482851472851072062143c3081ac3261a856482851482851572851072851072851072851072851072851572851482851472c3271a8515728510728510720621438525722c6518851072852472c3271a8514728510722c84280605838520828514828510728515828524820605438514728110828510720621438524728514828514722c8428851572851072c3071a8514728510728520728510728520728515721681058515728514828510728514722c801885157285147285107285107285157285157285107285148206058386084b8510728510728515828510728515728510728515828514728510728514828510722c8428851072852472851072851482851472851072c3261a2c651885147285107285107285207285107206214386264a8524728515728514828510728510722c84281681050605438510722c65188510722c8428851072060543852072851382851472811582c3081a9115828525728510728113822c84288510728560728515728510728510828510728510728514728510728515728510722c84288514820621438510722c84288510722c84288510722c64288523728514828510728510720621430605838524728515728514828510722c64288510728524728514722c65188515728514728510728510728515828515728510728165828510728115828510722c65180605438510728510722c65180605438510728510728515728510728115829514829125828510728514820605838514828510722c84288510728524728510728510728520728515728514728510722c65188120828520722c6518851572851572851072c3271a8510728510728524728514828510728515728514728515728510722c8428852572851072851572851072816482c3261a851472
    | 4 => 0x8515728510722c84288514828510728515728510722c85282c65188524728520728510722c8528851072851072851572851472851072851072c3081a85107249610c2c84288515728520728524828510729514828520728510728510720621438520728515728510728515828510728515728510728510728514725a08669125820605838520728510728515828510721681058510728520728514728510728510728514828510728514828514828510720605838514728524728520728514725308660605438520728514828510729115828510728514822c8428852072851072168205062683c3081a8520728514828510728515722c65188514722c80288520728510722c65188515728514728510728113828560728515722c8428851072c3261a8524728515728510728515728510728515828515728510728510728510722c8428851582851572851472851072851072c3271a8510728510728515728514828510728515728565728515828515728510728520728510721681058564828514828515728520728514828514728520728515728510722c84288514822c63288515728510728514828514728510722c6518c3271a8515722c6428851572851082811582851582851072c3271a8524728515728510728515828515728510722c85288510728510728514828514720605432c8428851482851472851372851072851482851072062143851482851072851072c3071a8510728514822c8428852072851572851072c3271a8525828515728514828510728514828514728515728514828510722c84288510728510728515728510722c84288510728515728510728515728514822c8528851572060543851472851072c3271ac3271a852472851072951482852072851072c3271a8515728510728510728510828510728564828525728515728510728560728514828514728510722c84288515820626438515728510722c84288515828515729514828510728510728520728515728510720605838515728510728564828515828510728515728514828510728514728510728510728515728515729125828524728514728510728510722c84188514722c84288520728514828110828514722c84288510722c6518c3261a8515728510720605439115828510728510722c84280605838515828510722c84282c6518c3271a851572851482c3271a852572851072851072851572851072852482851072060543851072165105851482851072852572851472851072851482851482851072062143851572852482851482851072062143851072851582851072c256188515728515828510728520728510722c84288510728514828510728524828510728515828510728510722c8428851572851482851072851572c3271a8520728510728514822c84288510728520720605838514828514828514728510728524728520728515728515728514728510728515728514828515728510722c85282c6518851572851472851072c3081a2c84288524728510722c84288514728510728515728510728520728515728514828510728510722c85288514822c65188515828510828510728115828514828514728514722c84288510728510722c84288515728515828510728510728515728514724318308515722c6518851072a4580c8520720605438510728560728515728510720621438510728510728515728514828524728510728525728510722c84288510728515728510722c84288510722c84288514828510722c84288510728520720621438515724a610c8515828514822c84288510722c8418852472851072851482851472851072852072851072c3081a8525728515728515728514722c84288510728510728515728510728510728514828514722c84288515828510728510728510728514828510722c8428851072c3071a8515728510722c84288515728515728515728510728510728524728520728510728520728514728515828510722c65188560728520728510728514722c8418851482851572851072c3271a9514828510728510728520728515728510728510726052438510722c8428851582851072060543856072851072851072851572851072
    | 5 => 0x8514728515828510722c8428851072852072851072060543851072851482851072851572812082852472852072c3271a8515728115828520728515828514822c6518951582851072851072c3271a8514828514728510722c84288510722c84288510728514828510728524728510722c8428851072851072851572851072851082851072851072c3271a8515728510722c84288510722c64288520728514728510722c84288510722c84288514828510722c84288510728515728510722c84288510728510728514828510720621438524828520728510722c8428851572851072851072811582c3281a8510722c65188520728510722c8428852072851072851572c3271a8515728510722c8428851582851072852072851072060543851072851072952482851482851072060583851072851072c3271a8510728510728514828524728510728510728510722c84288510722c65188514722c8428c3271a8510722c8428851582851072c3271a852072851482851572851072851072852072c3271a851072c3081a851572851072c3271a8520728510728510722c8528851072851072851072851472851072851072851072851582851072811082c258288510728515728514825325662c84288515728514828510722c8428c3261ac3081a2c64288515728510728510728515728514728510728510728510728520728510728510720726430605438520728515728510728510728113828510728515828510728515728515828515728514728510722c8428851572851482851072852072852482852072851072852072851472851072c3271a8564828510728515828510728510728520728524728515728510722c84288510728514828510721681058560722c8428851582852072851072c3261a8515728510722c84282c85288520728515728510728510728520728514728510728115822a8528851572c3261ac3271a851482851072851582851072530866851472851072c3081a8514828514728510728515722c8428851582851472851072c3271a8510828520728510728514728510728125828515828510728510722c84288514728510728115828560728510722c84288515728560728510728515728510728524822682358515728514822c65288515728514722c85282c64288515722c84288515728514828510720c28748510722c84288514828510728520728515728510720621438514828515728524728514728510728110822c65188514728510728510728515728514728510722c6518811582c3261ac3071a8525728520725081718510728510728510728510722c85288510728115828514728510728524728515728514728510728524722c84288515728510722c80182c84288510728510722c80288510728514728510720621438520728510728514828514822c75288510728514722c64288514728510728510728520728514820605838514822c65188514728510728520728515728514822c84288515728510728520728510722c6518852072851072911582851582851572851472851072c3271a8514828510720605438524728510722c84288510728510722c841885157249610c8515728510728514828510722c84288524728510722c8428851072851472851072851072062143c3081a2c65185941822c84288514728510728515728515728510728510722c84288514828510728520728514828510728115822c84288510720605838514828510728510728515728520728515728510728515728510728510728510728520728515728514728510722c8428851072851572851072851072851082852072851572c3271a9514828524828510728510729514828515728514828514728510728524828514728510722c8428062143c3271a8565728515728510722c84282c6518c3081a8514722c8428168105c3271a8510728510728510722c84282c65188515728510728520722c84288520728514828510728510722c6428852472168105851072c3271a851572851072852072851072851072264105c3071a8510728510722c8428951482852472851472851072851572851072060543851482851482851572851072851472851072851072
    | 6 => 0x851072952482851582851072168105c3271a8515728510728510728115828510728510728514728510722c8428060543c3271a8510728515728510722c651885158285107286084b8514728510728520728514820621438510728514828510722c6518851572851072851582851482852072851072851582851472851072851472852072851482851072072543851572851072851482851072c3271a8510728510728510722c84288520728515728515728525728515728524728510728520728510722c84288510728524728514828510728515728510728514728524828515728514728510728515728514728510722c85282c84288514828510728520728514728510722c84288514822c84288524728514728510722c84288520728515728514728520722c65188510728514728510728514822c84288514822c8428062143851072c3271a8520728510728115822c84288510728510722c84288510728514728514722c8428851072851072060543851572851572851482851572851072062143852472605243851572851482851072c3261a8515728510722c65188510722c84280605439515828514828510722c8428851572851472851072851572c3281a8510722c65182c6428851572c3271a8525828510728514728510728510728514828514722c84282c84282c6518851072c3271a8525728520722c8528c3261a8514728510720c2874c3261a8515828510722c8428852472851482851072852072851482851072851572851072851482851072062143c3271a85157285138285107285157285107284580c8120828515728510728524728510728520724358302c8428851072851572c3081a912582852072851482851572851482c3271a8510725308168510728520728514828524728515728524728510720605438515728510728520728510728510722c84282c84288514728510728514828560722c80288514828510728510728510728560728514728510728515728514728510722c8428852072851482190182062183c3271a851482851072851482851072c3261a2c84282c65288515728510722c8428852472851072851582851572851072851582851482851072851072851072852072851572851482851072852072851482852072851572851472851072851572851472c3271a8510728510722c84280605438515728510728510722c84288510728510728515728514728510720625438510728524728514828510728520728520728514728510728510722c8428851472851072856572851572851072851072851072851072851072851072851572851072851072851072852482851072605243851582060543851572851072851072c3271a508171851072c3271a8524828510728514828514722c65188560728515728510728560728514828514728510728510728564728515828510728524828514722c84288510722c84288520728515728510728524728510728525828510728515728510728510722c64288510728510728514828514728510722c84288520728510728515728514728510722c84288515720621430605438514828510728515728510728510720605432c84288515728510728514828510722c84288515828115822401318510728110828510729524828515728510722c8428851072851472851072851072851482851072c3271a852072851572851482851072060583c3081a8515728514828510728524722c842885247285107285148285107285207285107285247285158285107285257285107285107206054385107285157285157285148296064a8515828510720605838515728515728515722c84288525728524728510722c84288520728514828514728510722c65188510728520728515828515728524828510722c85282c8428b4270c85107285107285148285147285107269804b851482851072c3081a8520728510722c84288510722c84280605838514828510728514828510728515728514728510721681058520728510722c8428851072851572851482851472851072851072851072851482851472812082c3271a851472851082851072852472811582851482851072060543851482851072851572
    | 7 => 0x2c65180605438510728514828510728515728514828510728520728514828510728515728510728110828524728510728510728515822c84289515828510722c84288514828510728515828514728510722c8418852472856472851482851072c3061a8515728510728510728520728510722c6528060583851072240131c3271a8520728510722c65188510728510728510722c84288510728515728510722c8428851482c3271ac3081a851072852072851582851072852472851072c3271a851572851472c3071a8510720605838510728515728514822c65188510728510722c84182c84282c6328851472851572851072c3271a8520728515728510722c84282c8418851572851072851072851072c3081a8515828510722c84288520728515728510828510728115820621430605438514728510728510728515828515728510722c84282c6518851482851072168105c3271a8514828510728115828510728515828510728514728510720605838520728510728520728510728510728510728510728510728520728115822c85288515828510722c84288524822c84288510728510728515728510728510728524728510722c84288510720621438510722c6518060543851472851072852472851072851072851072c3081a852572851582851472851072852072851572c3271a851472851072851472851072c3271a8524728514728510728510728515828514828510728520728510722c84288510722c84280605838510722c84289514828520728524722c84282c8428c3261a8515828514828510722c8418c3071a8515728514822c84288514728524728515722c65180936888515828514828524728514828514728510722c8428851072811582851472851072851572851072851072851482851472851072c3271a8515728510728514728510722c84288514828510722c84288510728515728524828515728514728510728514822c84288514828515728510722c84282c8428060543856482851072851472851072851572851572851482851072851072c3071a8510722c84288510728510728510728514828510728510728510728514828514728510728515828510728514728120828510722c8428851572851072851072851482851472c3271a851072532866851472851072062683c3271a8510728514828510728510722401318520728515728514828510728510728520728510722c6428852482852082851482851072851072852072851572851482851572852072851072851072851572851072852572851482851472851072060543851572851072851072c3081a8514728510728515728510728510725081712c65188510728514728510722c84288510728515728510728510720605438524728510720605438510728510728510728510728514728510728514828510728115828520728510728560728520728510728510728520728514828514728510728510728510728525828510721681050605838510728510722c84288514828510728515828510728514828510728510728515722c84288510728514828510728524722c84288510728510728510728514828510722c84288515722c84288515722c84188520728510728515722c85282c84282c6518c3271a851072852072851482851072062143851572851072851482851072168105851572911582851482851072856472851072852072851582851572851072852482851072852072851572851072852482851072851072852072c3081a8510728524728514828510721681058515728524728510728515828510722c63288510720621432c85288510722c84288514828510728520728510728510728515728520728510729514828514822c8428852072851472851072851572c3071a8510722c8428852482851472c3261ac3081a851482851472851072851472851072c3081a856482852482851072c3071ac3061a8520728514828510728515728510722c84288510728510728520728515728514828513828510728514728510728510722c84280621438510722c84282c8428851572508171c3081a851072811582431830c3271a851582851482851482851072060583851482
    | 8 => 0x8524728510728515728510722c8418c3081a9524828520728510722c84180605438510722c8428851572851072c3271a2402318510728510728514828510722c65188510728515828515728510728520728515728514828510728515728514828510722c84282c6428851472851072851072c3271a8510728510728525820605838510728514828510728515828510728524828510728510720605438520728510728525728515728514728510722c8418851582851572851482851072851572851072851072856482851072851072c3271a8510728510728510722c6528851572851072c256188510728515728510728520728515722c84189514828510722c8428c3081a851572851072811582851072c3261a8524728520728510728510728510728520729564828520728510728510728515728510728520728510722c8428912582851072852072851572851072c3271a8515728510728510722c8428c3271a8564822c84288520728115822c64288510728510728510728514828510728510728514728510728514728510722c8428c3271a851472c3271a8524828515728510722c65188524728520728515728515728510728510722c84282c6518c3271a8515728510722c842885247285148285157285147285107285107286084b9514822c8428c3271a851072062143851072851482851072852472851572851072c3271a851072851072811082851482851572851482851072851072c3081a8510728510728515728514828514722c6518851072852072851482851072851072852072851072851072c256188520728510728514728510722a84288510728115828515728514822c84288510728115828514728510728510728510728510728514722c84282c84288514828510722c85282c84288520728514728510728515722c8428c3271a96084b8510728524728510728515728514828510722c8428851072851472851472c3081a8510722c64281681058520728514728510728510720605438510722c8528852072851072062143851472851072851572508671852072851572851072c3271a851572851482c3281a8510728115822c64288510722c84288115820605838510728514828510722c65188514822c65188515728510722c6428851072851072811082851072852072851072c3271a8510728525728510728115828515728510728510728510720605838515725081718520728514822c64288515728514728520728510722c84288514728510722c65188510728510722c85288520728515728514720605838514828514728515728510728520728515728514728510722c84282c65188515728510729514828510728514728510728510728510728520728524728515728514828515728510728510728515728510728510728510728514828514828510722c64282c84288115828515728510728125822c84281681058515728515822c84288514728510728510722c85288564828510728510728514828510722c65180605438510728510722c84288510722c64288510728510728515728510722c84288510728514828510728115828510728510722c84288514828510722c8428851572851072851072c3081a8514828510722c85288515728514821681052c84288514728510728510728110828510728520728510728515728510721681058515728510720605838515828510720621438515722c84288510728520728510722c84288514722682358525728515728514822c8528851072852572851072851482c3271a8515722c84288524828510728520728510728510728520728514828510722c84282c6518851072c3261a8514725328668514828510728510728114820726438514822c84288510725328668520728514828514828510728515728510728525728514828520728514728510722c8428851482c3271ac3261a851072070543c3261a8520728510728125828515728510722c84288510728514822c65188514822c84288520728514828510722c84288515728510728115828515728510722c8428240131851482851072851072951482851482c3271a852072851482851072268135851582b4160c8514828510722c6528
    | 9 => 0x8510729514828515728510720621438510728520728510728164828515725308660605432c85288510722c84288515828514828510728520728515728510829125828510728510729524828520728510728514722c8428851072851072851072852472851572851472851072851072851572851572851472851072812082c3081a8510721682058520728515828514728515728165828520722c74288510728510721641058515728514828514728510728514828510722c84288515828515728510728110828514728510720605438515728514829125828515728514822c8428852072851072851482851072060583851472851072c3081a8515728515828510722c84288515728510728510728520728510722c84288510720c2874851072060543851572c3271a851582851072851482c3261a8515728510728510728515728510728515828514728510722c84288560728510728515828524728510727514828514728524728520728520728510728515728513828510722c65184218318524728514828515828514728510728115828520728515728510722c8418856072851572851482851472851482851072c3071a2c84280605838520728515728520728515728510728510728514728514822c8528c3271a851572c3071a8564829125828524828520728510728515728520722c8428851072851582851572851072851072851072851072852472851572851072851072c3271a8564728520728515728510728110828520728514722c84288514728510728510728510722c84288524728510728510728514728510728514722c8428851472851072851482060543c3081a8515728510728520728515728510728510728515722c84280621438510728515828515728520728510728510728514828514720705438510722c65188524828510728514728510728515728510722c842885247285107285157285107206214385147285107285247285107285107285248285107269804b060543c3271a8514828520728515828510722c842885158285107281108286264a851572851082851072062143851482851072c3271a9525828514828510728515728514728514728510722c65188524728510728515728510722c8428c3271a8515728510722c8428856072851072c3081a8510728514822c651885107285207285107285247285107294164c8520728515728510728514828510728514828524828524722c84280605838510728515725308668514728510726c625a0621838510722c84288525728515728510722c84288514728520728510722c85288515828515728514828510722c84280605838514828510722c65182c8428093688851572851072c3271a8515728520722c8428c3271a8510728514728510722c8428c3081a8510725308662c6518851482851072851072c3271a8510728124828524728520728514728510722c65188510722c84280605438515728514828510728510728510722c8428852072851482c3081a85107285148269804b8520728510728524728514728510728560728510728515728514728514728510722c84282c65188520728510728520728514828510728514828515728110828515728520728510728560728523728510728510728524828520728514722c84282c84288510722c84288524728515828514728515728510728510722c8418851072c3081a8515828514728510728510722c65188515728515722c84289514828520728510722c84288510722c84288514828510728520728510728514728524728510728514828510728520722681358524828510728510728510720605838510828510728114828524828515728514828510728514822c65282c65188560728514728510729125828514728510728510722c84188514828514728510722c8428852072851472851072062143856072851482851072c3271a851472851072c3271ac3081a8510728510722c8428c3271a8515828515728510728515728510728564828510722c65188564828515728510722c84288510729125828515728514828510722c65188514728510722681358510728520728514828510720621430605438510722c8428851472
    | 10 => 0x8514729125825a08662c84288525728510728510728510828514828510728110828510728510722c85288510729514828515728510729524828510722c84288524828510722c8428851482851072851472060583c3271a8515728514728510728510728510722c84288520722c8528851072851072851572851072605243851572851072c3271a851482851072c3261a8510722c84288510722c84288510722c8428c3271a8515728520728515728510728564828520728513728510722c65188524728514828510828510728515828514728510728514728510728514728510728110822c85288514728515722c84288514828514728510728514828515728520728510728520728515828514728510728510728515728510728514728510728515828510728520728514822681058515828515728510722c84288514828510728514728565728524728510728515728514728510728515728510728515728510722c84288515728514828510722c84288524728520728510728520728510728510722c84288510728515728510728510720621432c84288514828510728510728515728510720c28748564828514828510722c84288514722c8428852072c3271a851472852482851072852072851072851572851072851072c3081a8510728510728560728514828514728510722c84288520728515728514728510728515828510728514728510728515728510722c84288524728514728510722c8428851072851072811582851072852072851072c3071a8515728510728510720605838514822c84282c85288515728510728564728560728510728510722c84288510728525828510728510728510728520728510720605438510728510728510728515728514728515828515728510720605838510722c84288515728510728510728510722c8528851072168105852072851072851572c3271a8510722c64288514728510728515728510728520722c84188520728510822c8418856072852072851072851572851072421831851072811582851072c3071a8514728510725308668520728514828514728510728515828514828510720605439524828524728510728510728515728510728515728524728510728515728510722c84288510728510728514728560728524728514828510722c74288510728514728510728520728524728510728520728515828510720605832c84280605838510728514828510728514828515728514728515828515728510728515728510728510728514728513728514828510720605838524728520728515726052432c64288515828510722c65188515728514728510728525728520728514728510728510728515828510728520728510728510720605438510722c8428851482851072060583851072811582851072852472851482851082851072851582851072851072c3261a8510728515720621438510721651058524828510723481302c84288510722c84282681358515728510828510728510720605830605438514724358308510728515728514728510828510722c64288524728514828510728515728510722682358510725308668510722c84280621438520728514728510728510722c8428c3271a851482851472851072851572851072060583851482851072c6265a851072c3271a8564828514828124828515728510728510722c84288520728510728515728510728514828510728510728520728510728514728510728560728510728515720605438515728510724a610c8524820605438510728510728510729514828520728515828514828510722c8428c3081a8514828510722c65180605438510728515728510728520728510728524828520728515728514728510728560728520728514828510728510728515728514828510722c84288510728515728510728510728514828510728510728510722c84288520728515828510722c64288510728510728115828520728515722c85288510722c6518851482851072851072851072851072856072851072852472851472852472c3271a8560728514722c84188514722c8428852072851482c3081a8510721681058514826052432c6518851572851582
    | 11 => 0x851072851582852072851572851072851472851072c3271a8510728515828510722c64188510728514728510722c84288515820605838515728510722c84280621438510728515722c84288520728510728514721681058520728514728515828510722c8428852472168105851072811582530866852072851572851072851572851572851072851572c3271a8510722c60288524728520728510728510722c84188510728510728510728510728515828510722c842885107249610c8514828510728525728520728510728520728510729514828560728514728510728514828510722681358510722c65180605838515728514728510722c85288510728524828510722c84288515728510728510722c6518c3271a8510728510720605432c8528871382851072951482851572851072340130c3271a8514722c65188514828510728515728510728514728510728524728510728510722c84282c74288520728510722c84289514828515728514828510722c6518851072851072c3081a8515728514828510728525722c84181681058524728510729514828510722c6518c3071a8525828515828510722c84188510728510722c8428851572851482851072060583852472851572852472851072348130851072060583851572851482851072c3081a9125828510722c84288514828510728515728514728510728515728510728515728514828514825086712c7428852482851472851072c3081a8514828514728510722c65188514828514828510728510722c84188514728510722681358514728510728515728514728510722c84182c65188510728510728514728510728524728510722c84288520728510728515828510722c84288520728514728510720621438514828510722c84288514828514728510728510728115828515728510728524728515828510728514722c6518c3271a851072060543852482851572851072060543c3271a2c8428c3271a8510828510722c8428852072851072851482851072851072852472852072c3271a8514728510721681058520728515720605838514820605438510728514828510720605832c84288510728510728515728514722c84288514728515728510728510722c65188510728514828510728515728510728510728520728510722c84288525728510728510722c8428851482851082c3271a8510728510722c8428851572851072851572851482c3271a8525722c8428851072c3271a8515728514722c64288510722c84282c6028851072851072852072851572851482851072851072851572851072508171851482
    | _ => 0
  (block >>> (24*(i % 512))) &&& 16777215

def roff8 (i : Nat) : Nat :=
  let block := match i / 512 with
    | 0 => 0x1bc0dd86e83731b88dc46e036e1b68dac6d03651b18d746ba35b1ac8d586a63521a88d386983471a20d0c68434019e8cf067233819a8cd06683331988cbc65e32d1968cb465832a1928c8863c31d18d8c6863231818c0c5862a3121888c4061a30a1840c1860a3041810c005fa2fc17d8bdc5e62f11780bbc5dc2ee1760ba45ce2e51720b805c02df16f0b705b02d516a0b485a02cc1648b205902c51620b0857e2bb15c0acc5662b11578ab85562a91548a9854c2a41518a8453c29d14d8a5852a29514a8a4c52228e1468a305162891430a044fc27d13d89e44ee27613989c84e026e13689ac4d626a13409984ca26313109844c226013009784ba25d12d89684b225712a894449e24c125892448c245121890447e23d11e08e447223611a08d046823111788b045622a11508a444a223110888043a21c10d086042e21610a084c4242121078838416209104881840c20510288104042000ff87f83f81fa0fc87e03ee1f40f887c03de1ed0f507a03cc1e60f187803bc1dc0ec875c3aa1d30e9073c39c1ce0e7072c3941c80e3871c38a1c20df86f43741b90dc06d43681b30d906c435a1a90d386903481a30d1068434019f0cf067433619a0cc06603301970cb06543261920c7062c3101860c2060430217f0be85e82ee1760ba85cc2e016f0b705ac2cc1660b105802ba15a0ac85582a214f0a7853c29c14e0a4051c28e1460a2050427e13e09e84e826c13309904c826413109784b025612a094049424412108f847423611b08d045c22c115089844421e10c085041c2060ff07d83e41ea0f507a03d01e40ef07783b01d60eb07303941c80e206e036c1b40d806b83581aa0d406a034c1a60d0067032c1920c9063030c1840c105f82f41780bb05d82ec1720b805a82cc1660b205802b415a0ac05502a414c0a605302901440a004e826c13209704a824c122090047023411808c0460228114089043821010608204081f80f207603a81d40e807303881b80d8069034819c0ce06303001800be05f02f01700b405a02b815c0ae05602b014c0a004e026012c09404a023811808604101f80f007403901b80d406803201700b405802c01500a8052027012008404002000f807003201800b8054026012008803c01e00d005802800e006002800c002000
    | 1 => 0x3689b40d9e6ce3669b28d8e6c53619b08d826bf35e1ae4d706b635a1accd646b03571ab0d526a73529a94d486a43511a84d3e69c34d9a6cd3469a34c1a60d2c6943499a48d226903479a30d126883431a0cd0468134099fccfc67c33d99eccec67233819c0cdc66e33619a8cd26683339988cc265e32e196ccb465932b1958cac6543291940c9e64e3259920c8c6443219908c7e63c31d98ecc7463731a98c8c6262e31698b0c5862931498a4c4c6243121890c446213101880c3c61d30c185cc2a6143091848c226103079830c146073031814c0a6022ff97f8bf85fb2fc97dcbec5f52fa17ccbe65f02f797b8bdc5ed2f697b0bd05e62f31794bc85e32f09778bb85dc2ed1760bae5d62ea1744ba05cf2e69724b8e5c62e2170cb7e5bd2de16ecb725b72da16c0b5e5ad2d616acb565aa2d41698b465a02cf9670b305972cb1650b265912c79634b165882c3961cb0c5842c195fcafa57c2bd15e0aee5742b915c0ade56d2b595a8acc5652b19584abe55c2ac9554aa65532a91548a9e54c2a4951ca8c5462a19504a8254029e94f4a7653929b14d4a6453229894c0a5e52e29694aca545272929488a4251e28d1460a2c5112881440a1e50e2871434a165062811404a004ff27f13f49f64f827c13e09ee4f727b13d09e44ef27793b49d84ea27513a89ce4e527113789ba4db26c935c9ae4d626993449a24d026793389964ca263931498a4c426093009804be25e12e89724b725a92cc9604ac25592a49524a725312949444a124f127493649924c126092c494248923c91c48c244921c90c48424091fc8fa47c23d91dc8ea47523a91cc8e046f23791b48da46b234119c8c8463231918c8c245e22e11648b245722a11488a244e225912088e446221910888044021e90ec87443721a90d086643321810b885842b21510a0850426211908083c41d20e906c83441820b105882a413207903881a40c205102481040420190048024001fe8ff07f43f91fa8fd47e83f21f88fb47d83e91f40f907c63e31f18f887c43e01ef0f707b63d81eb8f507a63d21e88f3879a3cc1e48f187883c21e00efc77a3bc1dc8ee076c3b31d90ec47603ad1d68ea87523a51d18e8474239f1ce0e707343981ca8e4c72038e1c70e3471638a1c40e107063811c00df86f837c
    | 2 => 0x515a8a5450a25511a88543ca1c50e2869434a1950b2851424a10507282d414a075032815406a0150027f53f69f74f9a7cd3e69f24f927c93e29f04f727b53d69ea4f4a7a13ce9e54f127853c09de4eea76d3b29d84eb27513a49d04e7a7393969ca4e4271d3889c34df26ed3729b74d9a6c135e9ad4d5a6a13489a14d0a68133899a4cba6593289904c7a63931a98c4c4a6213089814bfa5f92f69774bb25d52e69704b7a5b12d69694b3a58d2be95e4aea5692b29574ab25552a49524a8253d29c94d4a5a5252909474a3250d2869434a0a4f527893b49ca4e127093749aa4cd26693349924c926293049724b5254928493a499248923490a47523291948c2459228913488a44521e90e485242921090548124052008ff47f23f51f28f747b23d51ea8f247823b91d68ea47423951ca8e5471a3851bc8db46d23611ac8d546a23511a68d1468233919a8cd46523251928c546223091808be45da2e91708b745b22d91688b2457a2b91568ab455a2a91528a8454229d14c8a5452228913e89d44e227113489a44b224d12288e446a23111488644222090fc87c43d21e50f287943ca1dd0ec874439a1c10dc86d43521a50ca864431a1850be85c42da1610b085742b214d0a4851428213909c84b425a125092847422211108483f41f20f107683a41c20dd068832418a0c105a82c414a0a104e826412208d04482040f207103681940c205902a813408a04101e80f4062031014808402a00d0048014001ff8ffc7fe3ff1ff0ff67fa3fc9fd4fe87f33f99fc4fde7ed3f69fa0fcc7e33f11f7cfba7dc3ed9f64fae7d43e91f34f987cb3e49f1cf8c7c53e29f14f867c23e11ef8f7a7bb3dd1ee4f6a7b43d79eb4f587aa3d49ea0f4e7a63d29e84f3c79b3cc9e5cf2c7953c99e3cf1c78c3c51e1cf0a7843c11e04efe77d3be9de8ef07723b89dc0edc76c3b59da4ece7653b19d84ec075f3af1d74eb675a3ac9d5cea87533a91d44e9c74b3a49d1ce8c7433a11d04e8074039f1cf4e7873c39d1ce8e7073739a1cd0e667323981cb8e5872a3949c9ce487233911c78e3471938b9c58e2870f3871c34e1670a3849c24e107073821c08e0070037f1bf8df86fc37c9bd4de46f03779bb0dd66eb3751ba8dd46e73731b90dc66e136f9b7cdbc6dc36b9b5cdac6d3
    | 3 => 0x6a1b4fda76d3969bb4d1a66d3269734b5a58d296943499a48d236913485a3ed1f68eb46da36d1a68cb461a2ed15689b44da24d11688343da1ed0e6853425a0cd03680b4019fccfb67cb3dd9eccf367933c59daced67633b19d6ce7672b38d9c0ce066f33719b6cda66b33559a4cd1667b33d99cccc666332998ecc7663331598acc4661b309980cc065fb2f9976cba65cb2e196ecb665a32cd962cb165832bd95ccae656b2ad956caa65532a594cca5651327d93cc9d64d326192ec9764b3251928c92648b241918c8a644b219906c81640b201900c8063fb1f58f8c7a63d31dd8ecc7463931c58e0c6d636b1b18d4c69633b1858bac5d62db1658aec5562ab1498a0c4e626b135898c4a6233115888c4261f30e5870c3761ab0d1868c31617b0b9856c2a614b0a1850c24612308583ec1d60cb05982ac1560a3045820c0f6063021810c06601b009802bff5fe2fed7f4bf85fbafd57e6bf35f9afc97e2bee5f6afa97d0be75f12f817bebdf5eeaf697b2bd85eb2f517a6bd25e82f4179ebcd5e4af1d78ebc45e1af0d780bbf5dfaef977cbbb5dcaedd76abb35d82ebd75abab5d5aead754ba95d3ae99748ba35d1ae85740b9f5ce2e6d734b995cbae5d72cb955c9ae49724b905c72e31712b875c2ae11704b815c02e016fcb7e5bdade56f0b765baadd56e8b735b8adc16deb6c5b5adad6d4b665b1ad896c4b615b0ad816c0b5f5aead716b4b595ac2d616b0b575aaad496a0b4f5a6ad35698b4a5a4ad11684b415a0ad01680b3d59d2ce9670b3759aacd1666b335982cbd65cb2b595aca5650b285932c95646b22590ac8563cb1d58eac75632b1858c2c6162eb1658a2c51628b135892c41620b0e5852c2160ab03580abf95faafc57d2bdd5e8af3578abbd5daaea5752b995c8ae05702b795b8adc56e2b615b0ad756bab595acad1567ab39598aca564ab1d588ac4561ab09584ac1560aafd57aabc55daadd56aab55592ac5560aae556aaa9550aa7552aa91544aa054faa7d53ea9e54e2a6d534a9854baa5d52ea945492a3d51ea8d545aa21510a84540aa01500a8053f29f94f8a7a53ba9d14e6a72538a9bd4daa6b534a9a14cea66532298d4c4a5d52e296d4b2a5852ba9514a4a51528292d494a48523a91948ca4452028fd47ea3a51ca8d545ea2c
    | 4 => 0x84cc26212f09584a424211f08d845c22e115089843421610508183fc1f20f707a83cc1e20f107583a41ce0e5071837c1b60d906a833c19e0c9064830c1860bf05e82dc1660ab05582a414a0a5052828c14209d04d826412a093044822410e08103e81dc0ea07303881bc0d606903381940c606102f817c0ae055026811408603f01e80e406a02d01480a404e01f00d806402a00b0047ff3ff5ff6ff87fabfc9fe0fef7f73fb5fdafea7f4bfa1fc8fe37f1bf85fc0fe07eebf71fb8fd87ebbf5dfacfd27e8bf41f9cfcd7e53f25f8cfc37e0bf05f80fbe7ddbee9f6efb77db3ed1f66fb27d8bebdf5cfa97d3be99f4cfa67d33e99f4afa17cebe6df34f987cbbe4df24f8f7c5be29f10f867c2be0df02f807bfbdf9efaf7d7bd3dddeeaf747b9bdc9ee2f707b7bdb5ed6f687b33d91ec6f627aebd6deb4f5a7ad3d61eb0f567a93d45e9cf4c7a5bd29e90f467a23d09e82f3d79e3ce1e6ef35799bccde62f30797bcb1e54f287933c95e44f2178fbc71e32f1878bbc4de22f107883c41e1af0b784bc25e0ef07783bc19e06f02780bbfddfcefe77ebbf1df6efa77cbbe1deaef3778bbbdddaeec775bba9dd4ee7772bb91dc6ee2770bb85dc0ee076f3b6ddb4ed976c3b5ddaced2768bb39d9aecd766bb31d96eca7643b0dd82ec075ebaf5d76eb875bbaddd6ceb475a3ad1d66eb1757bab9d58eab7553aa5d52ea87533a8dd42ea074f3a79d3ae9974cba61d2ee9774bba4dd24e907473a31d14e89743ba19d08e82740ba01cfee7c73d39e1cece76739b9c9ce0e6c735399dccee66733398dcc2e6172eb975cb6e5b72cb965cb0e5672ab951ca4e4e726b92dc92e487233915c86e41720b8fdc7ce3d71db8e1c6ce3671ab8d1c66e32718b8bdc5ce2a7143895c48e1f70e386dc36e1a70d3865c2ae137083839c1ae0b703b815c08e047013809c02e006ffb7edbf0df66fab7d1be0dee6f6b7adbd2de66f1b789bbeddd6edb765bb2dd66eab751ba2dcf6e6b72db94dc86e43719b8adc36e0b705b7cdbd6dd36e1b6edb46d9b6b9b58da86d33689b44d9f6cfb675b3ad9c6cd3661b2ad946c7b639b1ad8c6c5b629b10d876c2b611b08d826bfb5f5af4d766bab5cdaded6c6b5b5a5aced666b1b585ac0d5d6adb569ab0d566aab549aa4d4e6a5b521a8cd46
    | 5 => 0xa06502a811406a02d012805401a00cffe7fd3fb9fd4fde7e93f39f8cfba7d73eb9f4cfa27cd3e59f24f8e7c73e29f0cf827c13dc9edcf6a7ad3d39e84f3a7993cb9e4cf167873c29df4eee7733b99db4eda76b3b49d9ceca7613ae9d64eae7533a79d3ce9a7473a19cfce7a73739a9cc4e5e72d3949c84e3a71b38a9c4ce2670f3859c14e0a7033809bf4df26f53769ba4dca6e136d9b64dae6d13689b3cd9a6c93629b04d766b935b9accd626ab3549a9cd4a6a534f9a74d326913479a3cd1a68b3439a14d0668334099f4cf667733999bccde66b332997ccba65732a9954caa6513289944ca264d3259924c8a64131f98fcc7a63931998bcc5a62d31698a4c4e6253129884c3e617309982cc0a5fb2fd97dcbde5eb2f497a4bd25e52f0976cbae5d52e9974cb9e5cb2e39714b825bf2de96ecb6a5b12d796a4b4e5a72d29684b3e59b2cc9654b2a58d2c59614af25732b795acace5632af9564aae5512a6952ca8a5452a29514a7653529794b4a525252909474a3a51b28c944ca1e50b28193fc9f24f727993c49da4e927393949ba4db26c935c9ae4d1266932498e4c525f92ec9724b525692a494a4a5250927c936497249923c91e48f246922490647d23d91d48de46923491948ba455227912c89244321f90dc86642d212908c83241920b904c822407202900c8023fd1fb8fcc7d63e71f28f8c7c23df1ee8f6c7aa3d31e88f3479a3c51e28eec76e3b51d88ebc75a3ab1d48e9474a3a11ce8e6c7323951c58e1c70637f1be8de46ee3731b88db46d23671b28d8c6c23611ad8d546a234f1a68d2c68e3431a08cfc67a33919b8cd466232b1938c8463631718b8c4461630b1848c1c60a30117f8bec5ea2f11758b9c5c22dd16b8b4459e2cb1628b0c5862c11608af456e2b51588ab45562a91548a9c5462a114d8a6452e29714a8a4c5162891418a044fa27b13a89bc4d6265130897c4ba25b12d89644ae253128894449224311f88e446a23511688ac45222710f887c432215108882c40e2030fe87dc3de1eb0f387943be1db0ea874c3a21cf0e6872438a1bf0dd86e436e1b50d886bc35a1ab0d586a434e1a70d386843361990ca86343121850be85e42ea1710b685ac2d21690b3859c2c215d0ad85642ae1550a985442961490a3851427a13b09b
    | 6 => 0x2e8173fb9f5ceee73739b9bdcd2e67731b985cbae55729b93dc9ee4b723b90dc7ae39719b8b5c56e29714b89dc4ae25712b885c3ee1970ab855c26e13709b84dc22e0f706b82dc0ee036ffb7e5bf2df56f6b7adbd6de76f0b77dbb2dd76ebb74dba2dcd6e4b715b82dbf6ddb6cdb5edad6d4b695b42d9f6ceb675b2ed976c8b635b1ad876c2b60daf6d756b8b5bdad6d696b0b57dab6d536a7b53da9ad496a3b515a7ed37699b4b5a52d29692b495a3ed19687b435a12d0567fb3ed9e2cef676b3a59c6cdf66cb35d9a2cd1665b32d992cc5660b2f596ecb765ab2d5966cad656b2a594aca3650b26592ac91648b23d916c83640b1f58f2c77638b1bd8dac6b632b18d8bec5b62cb1558a2c4f626b12588ac43620b0f5872c3561ab0d5862c2d613b095846c1d60bb055826c0b605b025806bff5fcafe57eabf35f8afad7d2be95f2af8d7babdd5ebaf5d7a2bcd5e4af0577ebbb5dbaed576abb35d6aea5746b9d5ceae6572ab915c6ae2d70ab815bcadcd6e2b6f5b7ad9d6cab615b0ad6d6b2b575a9ad3d696b495a2ad0567ab37597acbd65ab2d595acad656b2b594ac8d646b1d58dac6562eb13585ac15602afd57dabdd5e6af1576abad5caae556eab655aead3567ab2d58eac5562ab0557eabf55eaad5566aad554aa9553ea9754aaa45522a91547aa2d50aa8153ea9ed4f2a77538a9b54d6a67532a98d4baa5b52da9654aea53528a92d48ea43520a8f5472a35519a8b5456a29512a88543ea1b50aa84d41ea0b504a8053f29f14f7a7ad3d29e74f2a78d3be9df4eda76d3b29d94eba7553a69cf4e4a71d38e9c74e1a7053829bd4daa6c53629af4d6a6b53569a94d4a69533e99b4cca65532a98f4c7a63d30e9854bfa5f52f29714b7a5ad2d29674b1a57d2b29574aaa54d2a294b4a4a51d28a94149ea4e526292b495a4a524a91f48da46522290f487a42520690147fa3e51e68ef473a3951c28dd46ca34519a8c9462a30517e8bd45da2dd1668af455a2ad14a8a144fa27d13a89b44da25d12288f445a22d10a88343fa1fd0f6875438a1a50ce86742fa1750ba85942ba14d0a284f427a13d09a847422a10d07e83941ca0d506282f416a0ad04e823410
    | _ => 0
  (block >>> (13*(i % 512))) &&& 8191

def code7 (_ : Nat) : Nat := 0
def offset7 (i : Nat) : Nat :=
  let block := match i / 512 with
    | 0 => 0
    | _ => 0
  (block >>> (1*(i % 512))) &&& 1

def proof7 (i : Nat) : Nat :=
  let block := match i / 512 with
    | 0 => 0x8525822c6428c3081a8525828564728524822c65283c85388564726c625a2c64288564722c6028812482062643c3081a5328668110824350202c84282c6528c2462885647284564c2c65282c6028062183856472c6265ac564728524828515822c65188524728110822c65182c60280626838565828564728524722c65182c84188110822c6028c246288515821318202c60288564728524823c85382c6428c3281a2a60288524722c60282c64282a64282c65182a6428072643c564722c84282c60286c625a2c65188524822c65182c641896064b2c65180601433c801a2c64282c60188565828524822c6028852482c6085a8515725328660605435328660605832c60280626838564728525822c64185328665081712c60282c80282c6028c3081ac3061a9515728110822c6518c564728524728515723c85382c6428c3085a2c64288524828518720626432c60288524824a850c06218396064b8564720621438110826c625a2c84182c6028c3085ac3081a8525828110825325162c65282c60282c60188515828515722c65182c6428c3081a2c6518c3081a8564728524822c75282c64280605832c60288110820625434a610c8524722c80282c60280601438515722c602807264396064b0607430605430605838125822c60288564720601432c65182c6028c3061a851472856472060583c3281a06264384564c5081718524825c8028c56472c246282c65188564728524824a850c06054385647284564c2c602896064b8524828115028524822c65180605436012832c60282c84180626430621830605438524828564728524828565828524828110855325160621432c65282a64282c80288564728525822c65288564725328668524825325162c84288110820605838524828515724a610c6c625a2a6428060543c6265a4a610c2c63288564728524828110828524820905488565828564722c65188564724a610c8524822c64288565822c65280726438524828518722c65180605432c60280605438565828564728515828515726c805a2c6518060543c3061a8524722c84188565828110822a64282c60282a60280605439515722c65182c60282c6018062683c354388524822c60280605434a610c2c64182c65180607432c65288565825081713c801a2c63182a64288110858524820607832c8418852482856472852482851572c3081a8524828515720605838524824a610c2c6028c208288524822c65188524722c64288524828564725328662c65182a6428c3281a2a64280621438524823c801a2c65180621430605432c6028c3081a2c6028c3081ac256282c6028
    | _ => 0
  (block >>> (24*(i % 512))) &&& 16777215

def roff7 (i : Nat) : Nat :=
  let block := match i / 512 with
    | 0 => 0x2813e9f4f273389acce633097cae4b259247e35168ac56271087c3e170984c1e0b02813fdfcfd7e3e9eef478bc1d8ec753a1cae270381b6d66ab51a2d066b298ec7632f974ba5c2dd64b157ab954a853a9d4ea451a8542a04fa753a9b4ca6530974aa4d24904623112874320d027d3e1e8ea75399c8de6f369acd66a34194c6622f970b65b2d164ae5529940a04c251288e43200f47435188c45e2d160a04e27130904823110843e1b0d0602a15098481c0e058281006028100600
    | _ => 0
  (block >>> (9*(i % 512))) &&& 511

def basis := raw ++ [neg raw0,neg raw1]
def addEncodedGate (vs : List Sig) (code : Nat) : List Sig :=
  vs ++ [bin (decide (256 ≤ code)) (vs.getD ((code >>> 4) &&& 15) zero) (vs.getD (code &&& 15) zero)]
def decodeState : Nat → Nat → List Sig → List Sig
  | 0, bits, vs => vs.zipIdx.filterMap (fun (a,i) => if bits.testBit i then some a else none)
  | n+1, bits, vs => decodeState n (bits >>> 9) (addEncodedGate vs (bits &&& 511))
def count : Nat → Nat
  | 11 => 36
  | 10 => 480
  | 9 => 1175
  | 8 => 757
  | 7 => 0
  | _ => 1
def bins : Nat → Nat
  | 11 => 19
  | 10 => 241
  | 9 => 588
  | 8 => 379
  | 7 => 1
  | _ => 1
def code : Nat → Nat → Nat
  | 11 => code11
  | 10 => code10
  | 9 => code9
  | 8 => code8
  | 7 => code7
  | _ => fun _ => 0
def offset : Nat → Nat → Nat
  | 11 => offset11
  | 10 => offset10
  | 9 => offset9
  | 8 => offset8
  | 7 => offset7
  | _ => fun _ => 0
def hbins : Nat → Nat
  | 11 => 1
  | 10 => 118
  | 9 => 1829
  | 8 => 3561
  | 7 => 165
  | _ => 1
def proof : Nat → Nat → Nat
  | 11 => proof11
  | 10 => proof10
  | 9 => proof9
  | 8 => proof8
  | 7 => proof7
  | _ => fun _ => 0
def roff : Nat → Nat → Nat
  | 11 => roff11
  | 10 => roff10
  | 9 => roff9
  | 8 => roff8
  | 7 => roff7
  | _ => fun _ => 0

def frontierState (k i : Nat) := decodeState (12-k) (code k i) basis
def frontierHash (v : List Sig) : Nat :=
  (v.foldl (fun t a => t + ((((a.1.toNat % 1048573) * 65537 + a.2.toNat % 1048573 + 317) % 1048573)^3 % 1048573)) 0) % 1048573
def frontierMatch (k : Nat) (w : List Sig) : Bool :=
  let h := frontierHash w % bins k
  let lo := offset k h
  ((List.range (offset k (h+1) - lo)).any fun m =>
    decide (lo+m < count k) && w.isPerm (frontierState k (lo+m)))
lemma matches_ok (k : Nat) (h : ∀ i < count k, Impossible k 0 (frontierState k i))
    (w : List Sig) (yes : frontierMatch k w = true) : Impossible k 0 w := by
  obtain ⟨m,_,ok⟩ := List.any_eq_true.mp yes
  simp only [Bool.and_eq_true, decide_eq_true_eq,List.isPerm_iff] at ok
  have eq := (Finset.ext (fun a => List.mem_toFinset.trans (ok.2.mem_iff.trans List.mem_toFinset.symm)))
  unfold Impossible at *
  rw [eq]
  exact h _ ok.1

def span (p : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n+1, i => p i && span p n (i+1)
lemma span_ok {p n i} (h : span p n i = true) {j : Nat} (lo : i ≤ j) (hi : j < i+n) : p j = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp h
    by_cases e : i=j
    · exact e ▸ a
    · exact ih b (by omega) (by omega)
lemma span_join {p n i m} (a : span p n i = true) (b : span p m (i+n) = true) :
    span p (n+m) i = true := by
  induction n generalizing i with
  | zero => simpa using b
  | succ n ih =>
    rw [Nat.succ_add]
    obtain ⟨c,d⟩ := Bool.and_eq_true_iff.mp a
    exact Bool.and_eq_true_iff.mpr ⟨c,ih d (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using b)⟩

-- A table entry supplies a candidate witness. Its four pairs are checked on the actual wires.
def hintMatch (k : Nat) (v : List Sig) : Bool :=
  let h := frontierHash v % hbins k
  let lo := roff k h
  decide (v.length = k+1) && (List.range (roff k (h+1)-lo)).any fun m => hintCheck k v (proof k (lo+m))

lemma hintMatch_ok {k : Nat} {v : List Sig} (hn : v.Nodup) (yes : hintMatch k v = true) : Impossible k 0 v := by
  obtain ⟨m,_,test⟩ := List.any_eq_true.mp (Bool.and_eq_true_iff.mp yes).2
  exact hint_sound hn test

def coveredAt (k : Nat) (w : List Sig) : Bool := hintMatch k w || frontierMatch k w

lemma coveredAt_ok {k : Nat} {w : List Sig} (hn : w.Nodup)
    (lower : ∀ j < count k, Impossible k 0 (frontierState k j)) (yes : coveredAt k w = true) : Impossible k 0 w :=
  (Bool.or_eq_true_iff.mp yes).elim (hintMatch_ok hn) (matches_ok k lower w)

def middleAudit (k i : Nat) := let v := frontierState (k+1) i
  decide v.Nodup && !stepTest k 0 v (fun w => !coveredAt k w) (fun w => !coveredAt k w)

lemma middleAudit_ok {k i : Nat} (lower : ∀ j < count k, Impossible k 0 (frontierState k j))
    (ok : middleAudit k i = true) : Impossible (k+1) 0 (frontierState (k+1) i) := by
  simp only [middleAudit,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true'] at ok
  intro m hm h
  have child (w : List Sig) (hn : w.Nodup) (l : Nat) (le : l ≤ k) (hh : Restricted l 0 w.toFinset) : (!coveredAt k w) = true := by
    cases e : coveredAt k w
    · rfl
    · exact (coveredAt_ok hn lower e l le hh).elim
  exact Bool.false_ne_true (ok.2.symm.trans (reduced_step h hm ok.1 rfl child child))

lemma excluded7 : ∀ i < count 7, Impossible 7 0 (frontierState 7 i) := by
  intro i hi
  change i < 0 at hi
  omega
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b0 : span (middleAudit 7) 11 0 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b1 : span (middleAudit 7) 12 11 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b2 : span (middleAudit 7) 12 23 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b3 : span (middleAudit 7) 12 35 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b4 : span (middleAudit 7) 11 47 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b5 : span (middleAudit 7) 12 58 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b6 : span (middleAudit 7) 12 70 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b7 : span (middleAudit 7) 12 82 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b8 : span (middleAudit 7) 11 94 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b9 : span (middleAudit 7) 12 105 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b10 : span (middleAudit 7) 12 117 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b11 : span (middleAudit 7) 12 129 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b12 : span (middleAudit 7) 12 141 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b13 : span (middleAudit 7) 12 153 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b14 : span (middleAudit 7) 12 165 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b15 : span (middleAudit 7) 12 177 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b16 : span (middleAudit 7) 11 189 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b17 : span (middleAudit 7) 12 200 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b18 : span (middleAudit 7) 12 212 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b19 : span (middleAudit 7) 12 224 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b20 : span (middleAudit 7) 11 236 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b21 : span (middleAudit 7) 12 247 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b22 : span (middleAudit 7) 12 259 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b23 : span (middleAudit 7) 12 271 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b24 : span (middleAudit 7) 11 283 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b25 : span (middleAudit 7) 12 294 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b26 : span (middleAudit 7) 12 306 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b27 : span (middleAudit 7) 12 318 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b28 : span (middleAudit 7) 12 330 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b29 : span (middleAudit 7) 12 342 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b30 : span (middleAudit 7) 12 354 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b31 : span (middleAudit 7) 12 366 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b32 : span (middleAudit 7) 11 378 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b33 : span (middleAudit 7) 12 389 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b34 : span (middleAudit 7) 12 401 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b35 : span (middleAudit 7) 12 413 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b36 : span (middleAudit 7) 11 425 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b37 : span (middleAudit 7) 12 436 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b38 : span (middleAudit 7) 12 448 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b39 : span (middleAudit 7) 12 460 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b40 : span (middleAudit 7) 11 472 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b41 : span (middleAudit 7) 12 483 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b42 : span (middleAudit 7) 12 495 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b43 : span (middleAudit 7) 12 507 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b44 : span (middleAudit 7) 12 519 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b45 : span (middleAudit 7) 12 531 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b46 : span (middleAudit 7) 12 543 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b47 : span (middleAudit 7) 12 555 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b48 : span (middleAudit 7) 11 567 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b49 : span (middleAudit 7) 12 578 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b50 : span (middleAudit 7) 12 590 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b51 : span (middleAudit 7) 12 602 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b52 : span (middleAudit 7) 12 614 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b53 : span (middleAudit 7) 12 626 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b54 : span (middleAudit 7) 12 638 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b55 : span (middleAudit 7) 12 650 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b56 : span (middleAudit 7) 11 662 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b57 : span (middleAudit 7) 12 673 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b58 : span (middleAudit 7) 12 685 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b59 : span (middleAudit 7) 12 697 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b60 : span (middleAudit 7) 12 709 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b61 : span (middleAudit 7) 12 721 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b62 : span (middleAudit 7) 12 733 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level8b63 : span (middleAudit 7) 12 745 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma level8 : span (middleAudit 7) 757 0 = true :=
  (span_join (n := 378) (m := 379) (span_join (n := 189) (m := 189) (span_join (n := 94) (m := 95) (span_join (n := 47) (m := 47) (span_join (n := 23) (m := 24) (span_join (n := 11) (m := 12) level8b0 level8b1) (span_join (n := 12) (m := 12) level8b2 level8b3)) (span_join (n := 23) (m := 24) (span_join (n := 11) (m := 12) level8b4 level8b5) (span_join (n := 12) (m := 12) level8b6 level8b7))) (span_join (n := 47) (m := 48) (span_join (n := 23) (m := 24) (span_join (n := 11) (m := 12) level8b8 level8b9) (span_join (n := 12) (m := 12) level8b10 level8b11)) (span_join (n := 24) (m := 24) (span_join (n := 12) (m := 12) level8b12 level8b13) (span_join (n := 12) (m := 12) level8b14 level8b15)))) (span_join (n := 94) (m := 95) (span_join (n := 47) (m := 47) (span_join (n := 23) (m := 24) (span_join (n := 11) (m := 12) level8b16 level8b17) (span_join (n := 12) (m := 12) level8b18 level8b19)) (span_join (n := 23) (m := 24) (span_join (n := 11) (m := 12) level8b20 level8b21) (span_join (n := 12) (m := 12) level8b22 level8b23))) (span_join (n := 47) (m := 48) (span_join (n := 23) (m := 24) (span_join (n := 11) (m := 12) level8b24 level8b25) (span_join (n := 12) (m := 12) level8b26 level8b27)) (span_join (n := 24) (m := 24) (span_join (n := 12) (m := 12) level8b28 level8b29) (span_join (n := 12) (m := 12) level8b30 level8b31))))) (span_join (n := 189) (m := 190) (span_join (n := 94) (m := 95) (span_join (n := 47) (m := 47) (span_join (n := 23) (m := 24) (span_join (n := 11) (m := 12) level8b32 level8b33) (span_join (n := 12) (m := 12) level8b34 level8b35)) (span_join (n := 23) (m := 24) (span_join (n := 11) (m := 12) level8b36 level8b37) (span_join (n := 12) (m := 12) level8b38 level8b39))) (span_join (n := 47) (m := 48) (span_join (n := 23) (m := 24) (span_join (n := 11) (m := 12) level8b40 level8b41) (span_join (n := 12) (m := 12) level8b42 level8b43)) (span_join (n := 24) (m := 24) (span_join (n := 12) (m := 12) level8b44 level8b45) (span_join (n := 12) (m := 12) level8b46 level8b47)))) (span_join (n := 95) (m := 95) (span_join (n := 47) (m := 48) (span_join (n := 23) (m := 24) (span_join (n := 11) (m := 12) level8b48 level8b49) (span_join (n := 12) (m := 12) level8b50 level8b51)) (span_join (n := 24) (m := 24) (span_join (n := 12) (m := 12) level8b52 level8b53) (span_join (n := 12) (m := 12) level8b54 level8b55))) (span_join (n := 47) (m := 48) (span_join (n := 23) (m := 24) (span_join (n := 11) (m := 12) level8b56 level8b57) (span_join (n := 12) (m := 12) level8b58 level8b59)) (span_join (n := 24) (m := 24) (span_join (n := 12) (m := 12) level8b60 level8b61) (span_join (n := 12) (m := 12) level8b62 level8b63))))))
lemma excluded8 : ∀ i < count 8, Impossible 8 0 (frontierState 8 i) := by
  intro i hi
  apply middleAudit_ok excluded7
  exact span_ok level8 (Nat.zero_le _) hi
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b0 : span (middleAudit 8) 9 0 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b1 : span (middleAudit 8) 9 9 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b2 : span (middleAudit 8) 9 18 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b3 : span (middleAudit 8) 9 27 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b4 : span (middleAudit 8) 9 36 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b5 : span (middleAudit 8) 9 45 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b6 : span (middleAudit 8) 9 54 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b7 : span (middleAudit 8) 10 63 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b8 : span (middleAudit 8) 9 73 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b9 : span (middleAudit 8) 9 82 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b10 : span (middleAudit 8) 9 91 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b11 : span (middleAudit 8) 9 100 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b12 : span (middleAudit 8) 9 109 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b13 : span (middleAudit 8) 9 118 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b14 : span (middleAudit 8) 9 127 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b15 : span (middleAudit 8) 10 136 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b16 : span (middleAudit 8) 9 146 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b17 : span (middleAudit 8) 9 155 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b18 : span (middleAudit 8) 9 164 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b19 : span (middleAudit 8) 9 173 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b20 : span (middleAudit 8) 9 182 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b21 : span (middleAudit 8) 9 191 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b22 : span (middleAudit 8) 9 200 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b23 : span (middleAudit 8) 10 209 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b24 : span (middleAudit 8) 9 219 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b25 : span (middleAudit 8) 9 228 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b26 : span (middleAudit 8) 9 237 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b27 : span (middleAudit 8) 10 246 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b28 : span (middleAudit 8) 9 256 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b29 : span (middleAudit 8) 9 265 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b30 : span (middleAudit 8) 9 274 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b31 : span (middleAudit 8) 10 283 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b32 : span (middleAudit 8) 9 293 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b33 : span (middleAudit 8) 9 302 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b34 : span (middleAudit 8) 9 311 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b35 : span (middleAudit 8) 9 320 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b36 : span (middleAudit 8) 9 329 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b37 : span (middleAudit 8) 9 338 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b38 : span (middleAudit 8) 9 347 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b39 : span (middleAudit 8) 10 356 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b40 : span (middleAudit 8) 9 366 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b41 : span (middleAudit 8) 9 375 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b42 : span (middleAudit 8) 9 384 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b43 : span (middleAudit 8) 10 393 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b44 : span (middleAudit 8) 9 403 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b45 : span (middleAudit 8) 9 412 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b46 : span (middleAudit 8) 9 421 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b47 : span (middleAudit 8) 10 430 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b48 : span (middleAudit 8) 9 440 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b49 : span (middleAudit 8) 9 449 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b50 : span (middleAudit 8) 9 458 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b51 : span (middleAudit 8) 9 467 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b52 : span (middleAudit 8) 9 476 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b53 : span (middleAudit 8) 9 485 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b54 : span (middleAudit 8) 9 494 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b55 : span (middleAudit 8) 10 503 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b56 : span (middleAudit 8) 9 513 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b57 : span (middleAudit 8) 9 522 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b58 : span (middleAudit 8) 9 531 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b59 : span (middleAudit 8) 10 540 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b60 : span (middleAudit 8) 9 550 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b61 : span (middleAudit 8) 9 559 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b62 : span (middleAudit 8) 9 568 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b63 : span (middleAudit 8) 10 577 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b64 : span (middleAudit 8) 9 587 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b65 : span (middleAudit 8) 9 596 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b66 : span (middleAudit 8) 9 605 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b67 : span (middleAudit 8) 9 614 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b68 : span (middleAudit 8) 9 623 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b69 : span (middleAudit 8) 9 632 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b70 : span (middleAudit 8) 9 641 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b71 : span (middleAudit 8) 10 650 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b72 : span (middleAudit 8) 9 660 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b73 : span (middleAudit 8) 9 669 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b74 : span (middleAudit 8) 9 678 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b75 : span (middleAudit 8) 10 687 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b76 : span (middleAudit 8) 9 697 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b77 : span (middleAudit 8) 9 706 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b78 : span (middleAudit 8) 9 715 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b79 : span (middleAudit 8) 10 724 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b80 : span (middleAudit 8) 9 734 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b81 : span (middleAudit 8) 9 743 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b82 : span (middleAudit 8) 9 752 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b83 : span (middleAudit 8) 9 761 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b84 : span (middleAudit 8) 9 770 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b85 : span (middleAudit 8) 9 779 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b86 : span (middleAudit 8) 9 788 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b87 : span (middleAudit 8) 10 797 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b88 : span (middleAudit 8) 9 807 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b89 : span (middleAudit 8) 9 816 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b90 : span (middleAudit 8) 9 825 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b91 : span (middleAudit 8) 10 834 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b92 : span (middleAudit 8) 9 844 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b93 : span (middleAudit 8) 9 853 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b94 : span (middleAudit 8) 9 862 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b95 : span (middleAudit 8) 10 871 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b96 : span (middleAudit 8) 9 881 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b97 : span (middleAudit 8) 9 890 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b98 : span (middleAudit 8) 9 899 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b99 : span (middleAudit 8) 9 908 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b100 : span (middleAudit 8) 9 917 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b101 : span (middleAudit 8) 9 926 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b102 : span (middleAudit 8) 9 935 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b103 : span (middleAudit 8) 10 944 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b104 : span (middleAudit 8) 9 954 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b105 : span (middleAudit 8) 9 963 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b106 : span (middleAudit 8) 9 972 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b107 : span (middleAudit 8) 10 981 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b108 : span (middleAudit 8) 9 991 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b109 : span (middleAudit 8) 9 1000 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b110 : span (middleAudit 8) 9 1009 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b111 : span (middleAudit 8) 10 1018 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b112 : span (middleAudit 8) 9 1028 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b113 : span (middleAudit 8) 9 1037 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b114 : span (middleAudit 8) 9 1046 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b115 : span (middleAudit 8) 9 1055 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b116 : span (middleAudit 8) 9 1064 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b117 : span (middleAudit 8) 9 1073 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b118 : span (middleAudit 8) 9 1082 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b119 : span (middleAudit 8) 10 1091 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b120 : span (middleAudit 8) 9 1101 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b121 : span (middleAudit 8) 9 1110 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b122 : span (middleAudit 8) 9 1119 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b123 : span (middleAudit 8) 10 1128 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b124 : span (middleAudit 8) 9 1138 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b125 : span (middleAudit 8) 9 1147 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b126 : span (middleAudit 8) 9 1156 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level9b127 : span (middleAudit 8) 10 1165 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma level9 : span (middleAudit 8) 1175 0 = true :=
  (span_join (n := 587) (m := 588) (span_join (n := 293) (m := 294) (span_join (n := 146) (m := 147) (span_join (n := 73) (m := 73) (span_join (n := 36) (m := 37) (span_join (n := 18) (m := 18) (span_join (n := 9) (m := 9) level9b0 level9b1) (span_join (n := 9) (m := 9) level9b2 level9b3)) (span_join (n := 18) (m := 19) (span_join (n := 9) (m := 9) level9b4 level9b5) (span_join (n := 9) (m := 10) level9b6 level9b7))) (span_join (n := 36) (m := 37) (span_join (n := 18) (m := 18) (span_join (n := 9) (m := 9) level9b8 level9b9) (span_join (n := 9) (m := 9) level9b10 level9b11)) (span_join (n := 18) (m := 19) (span_join (n := 9) (m := 9) level9b12 level9b13) (span_join (n := 9) (m := 10) level9b14 level9b15)))) (span_join (n := 73) (m := 74) (span_join (n := 36) (m := 37) (span_join (n := 18) (m := 18) (span_join (n := 9) (m := 9) level9b16 level9b17) (span_join (n := 9) (m := 9) level9b18 level9b19)) (span_join (n := 18) (m := 19) (span_join (n := 9) (m := 9) level9b20 level9b21) (span_join (n := 9) (m := 10) level9b22 level9b23))) (span_join (n := 37) (m := 37) (span_join (n := 18) (m := 19) (span_join (n := 9) (m := 9) level9b24 level9b25) (span_join (n := 9) (m := 10) level9b26 level9b27)) (span_join (n := 18) (m := 19) (span_join (n := 9) (m := 9) level9b28 level9b29) (span_join (n := 9) (m := 10) level9b30 level9b31))))) (span_join (n := 147) (m := 147) (span_join (n := 73) (m := 74) (span_join (n := 36) (m := 37) (span_join (n := 18) (m := 18) (span_join (n := 9) (m := 9) level9b32 level9b33) (span_join (n := 9) (m := 9) level9b34 level9b35)) (span_join (n := 18) (m := 19) (span_join (n := 9) (m := 9) level9b36 level9b37) (span_join (n := 9) (m := 10) level9b38 level9b39))) (span_join (n := 37) (m := 37) (span_join (n := 18) (m := 19) (span_join (n := 9) (m := 9) level9b40 level9b41) (span_join (n := 9) (m := 10) level9b42 level9b43)) (span_join (n := 18) (m := 19) (span_join (n := 9) (m := 9) level9b44 level9b45) (span_join (n := 9) (m := 10) level9b46 level9b47)))) (span_join (n := 73) (m := 74) (span_join (n := 36) (m := 37) (span_join (n := 18) (m := 18) (span_join (n := 9) (m := 9) level9b48 level9b49) (span_join (n := 9) (m := 9) level9b50 level9b51)) (span_join (n := 18) (m := 19) (span_join (n := 9) (m := 9) level9b52 level9b53) (span_join (n := 9) (m := 10) level9b54 level9b55))) (span_join (n := 37) (m := 37) (span_join (n := 18) (m := 19) (span_join (n := 9) (m := 9) level9b56 level9b57) (span_join (n := 9) (m := 10) level9b58 level9b59)) (span_join (n := 18) (m := 19) (span_join (n := 9) (m := 9) level9b60 level9b61) (span_join (n := 9) (m := 10) level9b62 level9b63)))))) (span_join (n := 294) (m := 294) (span_join (n := 147) (m := 147) (span_join (n := 73) (m := 74) (span_join (n := 36) (m := 37) (span_join (n := 18) (m := 18) (span_join (n := 9) (m := 9) level9b64 level9b65) (span_join (n := 9) (m := 9) level9b66 level9b67)) (span_join (n := 18) (m := 19) (span_join (n := 9) (m := 9) level9b68 level9b69) (span_join (n := 9) (m := 10) level9b70 level9b71))) (span_join (n := 37) (m := 37) (span_join (n := 18) (m := 19) (span_join (n := 9) (m := 9) level9b72 level9b73) (span_join (n := 9) (m := 10) level9b74 level9b75)) (span_join (n := 18) (m := 19) (span_join (n := 9) (m := 9) level9b76 level9b77) (span_join (n := 9) (m := 10) level9b78 level9b79)))) (span_join (n := 73) (m := 74) (span_join (n := 36) (m := 37) (span_join (n := 18) (m := 18) (span_join (n := 9) (m := 9) level9b80 level9b81) (span_join (n := 9) (m := 9) level9b82 level9b83)) (span_join (n := 18) (m := 19) (span_join (n := 9) (m := 9) level9b84 level9b85) (span_join (n := 9) (m := 10) level9b86 level9b87))) (span_join (n := 37) (m := 37) (span_join (n := 18) (m := 19) (span_join (n := 9) (m := 9) level9b88 level9b89) (span_join (n := 9) (m := 10) level9b90 level9b91)) (span_join (n := 18) (m := 19) (span_join (n := 9) (m := 9) level9b92 level9b93) (span_join (n := 9) (m := 10) level9b94 level9b95))))) (span_join (n := 147) (m := 147) (span_join (n := 73) (m := 74) (span_join (n := 36) (m := 37) (span_join (n := 18) (m := 18) (span_join (n := 9) (m := 9) level9b96 level9b97) (span_join (n := 9) (m := 9) level9b98 level9b99)) (span_join (n := 18) (m := 19) (span_join (n := 9) (m := 9) level9b100 level9b101) (span_join (n := 9) (m := 10) level9b102 level9b103))) (span_join (n := 37) (m := 37) (span_join (n := 18) (m := 19) (span_join (n := 9) (m := 9) level9b104 level9b105) (span_join (n := 9) (m := 10) level9b106 level9b107)) (span_join (n := 18) (m := 19) (span_join (n := 9) (m := 9) level9b108 level9b109) (span_join (n := 9) (m := 10) level9b110 level9b111)))) (span_join (n := 73) (m := 74) (span_join (n := 36) (m := 37) (span_join (n := 18) (m := 18) (span_join (n := 9) (m := 9) level9b112 level9b113) (span_join (n := 9) (m := 9) level9b114 level9b115)) (span_join (n := 18) (m := 19) (span_join (n := 9) (m := 9) level9b116 level9b117) (span_join (n := 9) (m := 10) level9b118 level9b119))) (span_join (n := 37) (m := 37) (span_join (n := 18) (m := 19) (span_join (n := 9) (m := 9) level9b120 level9b121) (span_join (n := 9) (m := 10) level9b122 level9b123)) (span_join (n := 18) (m := 19) (span_join (n := 9) (m := 9) level9b124 level9b125) (span_join (n := 9) (m := 10) level9b126 level9b127)))))))
lemma excluded9 : ∀ i < count 9, Impossible 9 0 (frontierState 9 i) := by
  intro i hi
  apply middleAudit_ok excluded8
  exact span_ok level9 (Nat.zero_le _) hi
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level10b0 : span (middleAudit 9) 15 0 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level10b1 : span (middleAudit 9) 15 15 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level10b2 : span (middleAudit 9) 15 30 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level10b3 : span (middleAudit 9) 15 45 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level10b4 : span (middleAudit 9) 15 60 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level10b5 : span (middleAudit 9) 15 75 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level10b6 : span (middleAudit 9) 15 90 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level10b7 : span (middleAudit 9) 15 105 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level10b8 : span (middleAudit 9) 15 120 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level10b9 : span (middleAudit 9) 15 135 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level10b10 : span (middleAudit 9) 15 150 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level10b11 : span (middleAudit 9) 15 165 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level10b12 : span (middleAudit 9) 15 180 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level10b13 : span (middleAudit 9) 15 195 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level10b14 : span (middleAudit 9) 15 210 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level10b15 : span (middleAudit 9) 15 225 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level10b16 : span (middleAudit 9) 15 240 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level10b17 : span (middleAudit 9) 15 255 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level10b18 : span (middleAudit 9) 15 270 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level10b19 : span (middleAudit 9) 15 285 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level10b20 : span (middleAudit 9) 15 300 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level10b21 : span (middleAudit 9) 15 315 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level10b22 : span (middleAudit 9) 15 330 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level10b23 : span (middleAudit 9) 15 345 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level10b24 : span (middleAudit 9) 15 360 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level10b25 : span (middleAudit 9) 15 375 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level10b26 : span (middleAudit 9) 15 390 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level10b27 : span (middleAudit 9) 15 405 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level10b28 : span (middleAudit 9) 15 420 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level10b29 : span (middleAudit 9) 15 435 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level10b30 : span (middleAudit 9) 15 450 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level10b31 : span (middleAudit 9) 15 465 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma level10 : span (middleAudit 9) 480 0 = true :=
  (span_join (n := 240) (m := 240) (span_join (n := 120) (m := 120) (span_join (n := 60) (m := 60) (span_join (n := 30) (m := 30) (span_join (n := 15) (m := 15) level10b0 level10b1) (span_join (n := 15) (m := 15) level10b2 level10b3)) (span_join (n := 30) (m := 30) (span_join (n := 15) (m := 15) level10b4 level10b5) (span_join (n := 15) (m := 15) level10b6 level10b7))) (span_join (n := 60) (m := 60) (span_join (n := 30) (m := 30) (span_join (n := 15) (m := 15) level10b8 level10b9) (span_join (n := 15) (m := 15) level10b10 level10b11)) (span_join (n := 30) (m := 30) (span_join (n := 15) (m := 15) level10b12 level10b13) (span_join (n := 15) (m := 15) level10b14 level10b15)))) (span_join (n := 120) (m := 120) (span_join (n := 60) (m := 60) (span_join (n := 30) (m := 30) (span_join (n := 15) (m := 15) level10b16 level10b17) (span_join (n := 15) (m := 15) level10b18 level10b19)) (span_join (n := 30) (m := 30) (span_join (n := 15) (m := 15) level10b20 level10b21) (span_join (n := 15) (m := 15) level10b22 level10b23))) (span_join (n := 60) (m := 60) (span_join (n := 30) (m := 30) (span_join (n := 15) (m := 15) level10b24 level10b25) (span_join (n := 15) (m := 15) level10b26 level10b27)) (span_join (n := 30) (m := 30) (span_join (n := 15) (m := 15) level10b28 level10b29) (span_join (n := 15) (m := 15) level10b30 level10b31)))))
lemma excluded10 : ∀ i < count 10, Impossible 10 0 (frontierState 10 i) := by
  intro i hi
  apply middleAudit_ok excluded9
  exact span_ok level10 (Nat.zero_le _) hi
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level11b0 : span (middleAudit 10) 9 0 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level11b1 : span (middleAudit 10) 9 9 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level11b2 : span (middleAudit 10) 9 18 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma level11b3 : span (middleAudit 10) 9 27 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma level11 : span (middleAudit 10) 36 0 = true :=
  (span_join (n := 18) (m := 18) (span_join (n := 9) (m := 9) level11b0 level11b1) (span_join (n := 9) (m := 9) level11b2 level11b3))
lemma excluded11 : ∀ i < count 11, Impossible 11 0 (frontierState 11 i) := by
  intro i hi
  apply middleAudit_ok excluded10
  exact span_ok level11 (Nat.zero_le _) hi

lemma root_ok {v : List Sig} (hn : v.Nodup)
    (test : stepTest 11 0 v (fun w => !frontierMatch 11 w) (fun w => !frontierMatch 11 w) = false) :
    Impossible 12 0 v := by
  apply exclude_step hn _ _ test <;> intro w hw <;> exact matches_ok 11 excluded11 w (by simpa using hw)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma ordinary : Impossible 12 0 raw :=
  root_ok (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma signedHigh : Impossible 12 0 (raw ++ [neg raw1]) :=
  root_ok (by decide +kernel) (by decide +kernel)
end PEqualNP.Outside.L_meta_3143

theorem PEqualNP.Outside.L_meta_3143 : ∀ (x1 : Fin (8 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x4 : Fin (8 : ℕ) → Bool), x2.eval (List.ofFn x4 ++ [!x4 x1, Bool.true, Bool.false]) = (fun (x5 : Fin (8 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (37 : ℕ), (46 : ℕ), (57 : ℕ), (74 : ℕ)].any fun (x6 : ℕ) => x5 (Fin.ofNat (8 : ℕ) (x6 / (10 : ℕ))) && x5 (Fin.ofNat (8 : ℕ) (x6 % (10 : ℕ)))) x4) → (13 : ℕ) ≤ x2.size :=
  PEqualNP.Outside.L_meta_3143.lift PEqualNP.Outside.L_meta_3143.ordinary PEqualNP.Outside.L_meta_3143.signedHigh
