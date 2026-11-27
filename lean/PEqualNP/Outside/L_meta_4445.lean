import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4445_aux.Theta

-- Each sampled signal carries its phase. The four binary operations represent AND and OR on signed inputs, and inverting a signal changes only its phase.
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

end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta

-- Trace the output backwards and keep the signals that still feed a gate. Each step uses one binary gate. Every surviving set separates every sampled pair, and its cardinality is at most one more than the remaining gate count.
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
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta

-- The search enumerates distinct operands, the four signed operations and the four choices of which operands are needed again.

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
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta

-- A restriction can force several live signals to zero. Projecting the rest of a trace saves at least one binary gate for each such signal.

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
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta

-- A restricted bank keeps selected pairs of rows. Duplicate one retained pair in the other positions to preserve the two-column representation.
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
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta

-- The certificate selects a restriction or enumerates a complete level of successors. Its hints can select any bank. Soundness follows from the projected trace and complete successor enumeration.
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

end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta

-- Permutations of sampled row pairs preserve every gate operation and the condition that the output separates all pairs.
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
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta
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
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta

-- A stored bound proves that a smaller set of signals needs a stated number of gates. A receipt reconstructs all the restricted live signals from that set. Combining the bound with the zero signals lost by restriction excludes the proposed continuation.
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
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta

-- The 87 pairs below differ in one input bit. Every pair contains one positive and one negative assignment for the specified graph.
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
theorem trace (C : Circuit) (fan : FanInTwo C) (eq : circuitFun 7 C=graph) :
    ∃ k≤C.gates.countP counted, Live 87 k inputs.toFinset := by
  let final := execute C.gates seeds
  let out := final.getD C.output zero
  have ev (i : ℕ) : read i out = C.eval (seeds.map (read i)) := by
    rw [show read i out = (final.map (read i)).getD C.output false from (read_get i final C.output).symm]
    rw [show final=execute C.gates seeds from rfl,execute_read i _ _ fan];rfl
  have result (x : Fin 7 → Bool) : C.eval (List.ofFn x)=graph x := congrFun eq x
  have good : Good 87 out.2 := by
    intro i hi same
    let j : Fin 87 := ⟨i,hi⟩
    have diff : read i out=read (87+i) out := by simp [read,same]
    have p := ev i;have n := ev (87+i)
    rw [(listed j).1,result,(labels j).1] at p
    rw [(listed j).2,result,(labels j).2] at n
    rw [p,n] at diff;contradiction
  have nz : out.2≠0 := by
    intro z;have bad := good 0 (by decide);simp [z] at bad
  have found : out.2∈ reps final := (get_simple final C.output).resolve_left nz
  obtain ⟨k,S,limit,live,sub⟩ := extract good nz C.gates seeds found
  have stays : ∀ a∈S, a∈inputs := by simpa [reps,seeds,List.map_map,Function.comp_def] using sub
  exact ⟨k,limit,initial live stays ▸ live⟩
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta

-- The matching upper bound groups the eight edges at vertices 1, 4, 5 and 6.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def eleven : Circuit := ⟨[⟨.or,[0,2]⟩,⟨.or,[7,5]⟩,⟨.and,[1,8]⟩,⟨.and,[0,4]⟩,⟨.and,[3,5]⟩,
    ⟨.or,[2,4]⟩,⟨.or,[12,3]⟩,⟨.and,[6,13]⟩,⟨.or,[9,10]⟩,⟨.or,[11,14]⟩,⟨.or,[15,16]⟩],17⟩
theorem upper_fan : FanInTwo eleven := by
  intro g hg
  simp only [eleven,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with h|h|h|h|h|h|h|h|h|h|h <;> subst g <;> simp
theorem upper_cost : eleven.gates.countP counted=11 := by decide +kernel
theorem upper_match : circuitFun 7 eleven=graph := by
  funext x
  have all : ∀ a b c d e f g : Bool, circuitFun 7 eleven ![a,b,c,d,e,f,g] = graph ![a,b,c,d,e,f,g] := by decide +kernel
  have tab : x = ![x 0,x 1,x 2,x 3,x 4,x 5,x 6] := by funext i;fin_cases i <;> rfl
  conv_lhs => rw [tab]
  conv_rhs => rw [tab]
  apply all
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta

-- These are all 84 possibilities after the first live binary gate. The lists of transpositions below are graph automorphisms acting on the 87 pairs.
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
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta

-- The orbit identities reduce the first layer to 28 representatives.
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
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta

-- These 41 restricted instances are checked independently. The receipts below contain at most two binary operations for each retained symmetry representative.
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
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc0 : Excluded 87 9 s00 := offAudit (g:=(.saved 0)) certifiedDB (by decide) (by decide +kernel)
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta
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
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc2 : Excluded 87 9 s02 := offAudit (g:=(.saved 0)) certifiedDB (by decide) (by decide +kernel)
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc4 : Excluded 87 9 s04 := offAudit (g:=(.saved 0)) certifiedDB (by decide) (by decide +kernel)
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta
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
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc6 : Excluded 87 9 s06 := offAudit (g:=(.saved 0)) certifiedDB (by decide) (by decide +kernel)
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta
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
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc8 : Excluded 87 9 s08 := offAudit (g:=(.saved 0)) certifiedDB (by decide) (by decide +kernel)
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta
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
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta
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
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc11 : Excluded 87 9 s11 := offAudit (g:=(.saved 0)) certifiedDB (by decide) (by decide +kernel)
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta
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
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta
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
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta
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
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc20 : Excluded 87 9 s20 := offAudit (g:=(.saved 0)) certifiedDB (by decide) (by decide +kernel)
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta
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
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc22 : Excluded 87 9 s22 := offAudit (g:=(.saved 6)) certifiedDB (by decide) (by decide +kernel)
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc23 : Excluded 87 9 s23 := offAudit (g:=(.saved 0)) certifiedDB (by decide) (by decide +kernel)
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc24 : Excluded 87 9 s24 := offAudit (g:=(.saved 6)) certifiedDB (by decide) (by decide +kernel)
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta
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
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc26 : Excluded 87 9 s26 := offAudit (g:=(.saved 6)) certifiedDB (by decide) (by decide +kernel)
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta
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
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc40 : Excluded 87 9 s40 := offAudit (g:=(.saved 0)) certifiedDB (by decide) (by decide +kernel)
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta
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
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc42 : Excluded 87 9 s42 := offAudit (g:=(.saved 7)) certifiedDB (by decide) (by decide +kernel)
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc56 : Excluded 87 9 s56 := offAudit (g:=(.saved 7)) certifiedDB (by decide) (by decide +kernel)
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc57 : Excluded 87 9 s57 := offAudit (g:=(.saved 13)) certifiedDB (by decide) (by decide +kernel)
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc58 : Excluded 87 9 s58 := offAudit (g:=(.saved 7)) certifiedDB (by decide) (by decide +kernel)
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux.Theta
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
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem resolved : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x1 = fun (x3 : Fin (7 : ℕ) → Bool) => [((0 : Fin (7 : ℕ)), (1 : Fin (7 : ℕ))), ((1 : Fin (7 : ℕ)), (2 : Fin (7 : ℕ))), ((0 : Fin (7 : ℕ)), (4 : Fin (7 : ℕ))), ((1 : Fin (7 : ℕ)), (5 : Fin (7 : ℕ))), ((2 : Fin (7 : ℕ)), (6 : Fin (7 : ℕ))), ((3 : Fin (7 : ℕ)), (5 : Fin (7 : ℕ))), ((4 : Fin (7 : ℕ)), (6 : Fin (7 : ℕ))), ((6 : Fin (7 : ℕ)), (3 : Fin (7 : ℕ)))].any fun (x4 : Fin (7 : ℕ) × Fin (7 : ℕ)) => x3 x4.1 && x3 x4.2) → (11 : ℕ) ≤ List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x5 : ℕ) => Bool.true) Bool.true x4.op) x1.gates := by
  intro C fan eq
  have same : (fun g : PEqualNP.CircuitLowerBounds.Gate => PEqualNP.CircuitLowerBounds.GateOp.rec (motive := fun _ => Bool) true true false (fun _ => true) true g.op)=counted := by
    funext g;rcases g with ⟨op,ins⟩;cases op <;> rfl
  rw [same]
  by_contra small
  obtain ⟨k,lim,live⟩ := trace C fan eq
  exact theta_excluded ⟨k,by omega,live,by decide +kernel⟩
end PEqualNP.Outside.L_meta_4445_aux.Theta

namespace PEqualNP.Outside.L_meta_4445_aux
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

inductive Live (target : Sig) : Nat → Nat → Finset Sig → Prop
  | stop (hp : proper target) : Live target 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) :
      Live target (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) :
      Live target (k+1) t (insert a (insert b U))

private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h with
  | stop hp => simp
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

private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
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

private lemma gate_rep (w : List Sig) (g : Gate)
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
private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
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
        have ht : Live target k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
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
        have ht : Live target k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
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

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live target k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]




abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop := v ∈ pool ∨ Constant v

def supply {R} (pool xs : List (Wire R)) := ∀ a ∈ xs, Available pool a

inductive Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | start : Reach roots 0 roots
  | one {p bank a} : Reach roots p bank → Available bank a →
      Reach roots (p+1) (inv a :: bank)
  | two {p bank a b} (op : Bool) : Reach roots p bank → Available bank a →
      Available bank b → Reach roots (p+1) (combine op a b :: bank)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

inductive Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop
  | stop : Run goal 0 [goal]
  | perm {s xs zs} : xs.Perm zs → Run goal s xs → Run goal s zs
  | one {s a rest} (save : Bool) : Run goal s (inv a :: kept save a rest) →
      Run goal (s+1) (a::rest)
  | two {s a b rest} (op ka kb : Bool) :
      Run goal s (combine op a b :: kept ka a (kept kb b rest)) →
      Run goal (s+1) (a::b::rest)

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩

theorem available_cons {R} {bank v} (w : Wire R) (h : Available bank v) :
    Available (w::bank) v := by
  exact h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr

theorem extend_one {R} (roots : List (Wire R)) {p bank a} (hp : Reach roots p bank)
    (ha : Available bank a) :
    ∃ q next, Reach roots q next ∧ Available next (inv a) ∧
        (∀ v, Available bank v → Available next v) ∧ q+cost a ≤ p+1+cost (inv a) := by
  classical
  by_cases c : Constant a
  · exact ⟨p,bank,hp,Or.inr (inv_constant c),fun _ h => h,by simp [cost,c,inv_constant c]⟩
  · exact ⟨p+1,_,Reach.one hp ha,Or.inl (by simp),fun _ h => available_cons _ h,by simp [cost,c]⟩

theorem extend_two {R} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (combine op a b) ∧
        (∀ v, Available bank v → Available next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next, Reach roots q next ∧ Available next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @one s a rest save _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_one roots hp (hs a (by simp))
    have ht : supply T (inv a :: kept save a rest) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · exact inc v (hs v (List.mem_cons.mpr (mem_kept hh)))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a rest save
    rw [mass_cons] at hl ⊢
    exact ⟨q,W,hW,hv,by omega⟩
  | @two s a b rest op ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_two roots op hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (combine op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_run {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | one save _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    exact Run.one save ih
  | two op ka kb _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    cases op
    · exact Run.two false ka kb ih
    · exact Run.two true ka kb ih

theorem projected_bound {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach roots p bank) (hs : supply bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach roots q bs → Available bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega


abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Bool) (a b : Sig) :
    observe (bin d a b) = combine d (observe a) (observe b) := by
  funext r
  cases d <;> exact bit_bin _ _ _ _

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {T : Sig} {k u S} (h : Live T k u S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run (observe T) k (v.map observe) := by
  classical
  induction h generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @unary k u U a ha fresh _ ih =>
    let rest := (U.erase a).toList
    let save := decide (a ∈ U)
    let tail := kept save a rest
    have er : rest.toFinset = U.erase a := by simp [rest]
    have hm : a ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have ht : tail.toFinset = U := by
      rw [show tail=kept save a rest by rfl,kept_fin,er]
      by_cases hh : a ∈ U <;> simp [save,hh]
    have nd := kept_nd save a rest hr hm
    have hf : neg a ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
    have progress := ih (neg a::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    rw [List.map_cons,map_kept,obs_neg] at progress
    have perm : (a::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm,hr⟩) hv
      simp [er,eqv]
    exact Run.perm (perm.map _) (Run.one save progress)
  | @binary k u U a b d ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d ka kb progress)


theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_bin (d : Bool) (f g : Wire Row) :
    table (combine d f g) = bin d (table f) (table g) := by
  rw [←table_observe (bin d (table f) (table g)),obs_bin,observe_table,observe_table]

theorem available_rep {bank : List (Wire Row)} {a} (h : Available bank a) :
    represented (bank.map table) (table a) := by
  rcases h with hm | ⟨b,rfl⟩
  · exact Or.inl (List.mem_map_of_mem hm)
  · apply Or.inr
    cases b
    · have z : table (fun _ => false) = zero := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_zero ⟨j,hj⟩).symm
      exact fun hp => hp.1 z
    · have z : table (fun _ => true) = one := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_one ⟨j,hj⟩).symm
      exact fun hp => hp.2 z

theorem inv_rep {w a} (ha : represented w a) :
    represented w (neg a) ∨ witness w (neg a) := by
  rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr fun h => h.2 neg_laws.1)
  · exact Or.inl (Or.inr fun h => h.1 neg_laws.2)
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)

theorem pull_cons {w : List Sig} {z : Sig} {T k t S} (h : Live T k t S)
    (hz : represented w z ∨ witness w z) (hs : ∀ a ∈ S, a ∈ z::w) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live T k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  apply pull_gate h hz
  intro a hm
  simpa [or_comm] using hs a hm

theorem reach_live_sub {roots : List (Wire Row)} {p bank}
    (h : Reach roots p bank) {T k t S} (run : Live T k t S)
    (sub : ∀ a ∈ S, a ∈ bank.map table) :
    ∃ l v U, l ≤ p+k ∧ Live T l v U ∧ ∀ a ∈ U, a ∈ roots.map table := by
  induction h generalizing k t S with
  | start => exact ⟨k,t,S,by omega,run,sub⟩
  | @one p bank a h ha ih =>
    rw [List.map_cons,table_inv] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (inv_rep (available_rep ha)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,table_bin] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (bin_rep d (available_rep ha) (available_rep hb)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩

theorem reach_live {roots : List Sig} {p bank T} (hp : proper T)
    (h : Reach (roots.map observe) p bank) (hit : Available bank (observe T)) :
    ∃ k t S, k ≤ p ∧ Live T k t S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,v,U,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,v,U,by omega,hr,?_⟩
  simpa [List.map_map,Function.comp_def,table_observe] using hs

theorem live_row_difference {T k t S} (h : Live T k t S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @unary k t U a hp hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · refine ⟨a,by simp,?_⟩
      exact fun he => hd (by rw [bit_neg,bit_neg,he])
    · exact ⟨v,Finset.mem_insert_of_mem hu,hd⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {T k t S} (h : Live T k t S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def seed : Sig := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed_table : ∀ r : Row, bit r seed = (sample r 0 && sample r 2) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem seed_nonzero : seed ≠ zero := by decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl

theorem exec_extends (gs : List Gate) (ws : List Sig) : ∃ l, execute gs ws = ws ++ l := by
  induction gs generalizing ws with
  | nil => exact ⟨[],by simp [execute]⟩
  | cons g gs ih =>
    obtain ⟨l,hl⟩ := ih (ws++[gv ws g])
    exact ⟨gv ws g::l,by simpa [execute,List.append_assoc] using hl⟩


def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r

def Lower (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map observe) p bank → Available bank (observe T) → L ≤ p


theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : represented ([] : List Sig) v := by
    have avail : Available ([] : List (Wire Row)) (observe v) := Or.inr ⟨b,h⟩
    simpa only [List.map_nil,table_observe] using available_rep avail
  exact (hr.resolve_left (by simp)) hv


def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)

def first : Sig := bin true (inputs.getD 4 zero) (inputs.getD 6 zero)

def rawMask (j : Fin 3) : Nat := [81, 84, 208].getD j.val 0

def extra (j : Fin 3) : Nat := [0, 2, 7].getD j.val 0

def second (j : Fin 3) : Sig := bin true first (inputs.getD (extra j) zero)

def bank (j : Fin 3) : List Sig := inputs ++ [first, second j]

def exactEdge (x : Fin 9 → Bool) : Bool :=
  ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List Nat).any
    fun code => x (Fin.ofNat 9 (code / 10)) && x (Fin.ofNat 9 (code % 10))

def encodedRows (j : Fin 3) (x : Fin 9 → Bool) : Fin 11 → Bool :=
  Fin.snoc (Fin.snoc x (x 4 || x 6))
    (decide (∃ i : Fin 9, (rawMask j).testBit i.val = true ∧ x i = true))

private theorem graph_exact : ∀ r : Row, bit r graph = exactEdge (sample r) := by
  decide +kernel

private theorem second_exact : ∀ (j : Fin 3) (r : Row),
    bit r (second j) =
      decide (∃ i : Fin 9, (rawMask j).testBit i.val = true ∧ sample r i = true) := by
  decide +kernel

private theorem ofFn_two (x : Fin 9 → Bool) (a b : Bool) :
    List.ofFn (Fin.snoc (Fin.snoc x a) b) = List.ofFn x ++ [a, b] := by
  rfl

private theorem bank_bits (j : Fin 3) (r : Row) :
    (bank j).map (bit r) = List.ofFn (encodedRows j (sample r)) := by
  unfold encodedRows bank
  rw [ofFn_two, List.map_append, List.map_cons, List.map_cons, List.map_nil,
    ← sampled, second_exact]
  simp only [first, bit_bin, ite_true, sample] <;> rfl

private def distinguishing (j : Fin 3) (i : Fin 9) : Row :=
  Fin.ofNat 512
    (([[16, 1, 2, 4, 65, 1, 18, 4, 8], [2, 1, 18, 4, 65, 1, 18, 4, 8],
       [2, 1, 2, 4, 65, 1, 18, 20, 8]] : List (List Nat)).getD j.val [] |>.getD i.val 0)

private def flipped (j : Fin 3) (i : Fin 9) : Row :=
  Fin.ofNat 512 ((distinguishing j i).val ^^^ (1 <<< i.val))

private theorem distinguishing_ok : ∀ (j : Fin 3) (i : Fin 9),
    (bit (distinguishing j i) graph != bit (flipped j i) graph) &&
    ((bank j).all fun w => w == inputs.getD i.val zero ||
      bit (distinguishing j i) w == bit (flipped j i) w) = true := by
  decide +kernel

theorem raw_in_every_root (j : Fin 3) {k t S} (run : Live graph k t S)
    (sub : ∀ v ∈ S, v ∈ bank j) : inputs.toFinset ⊆ S := by
  intro v hv
  have hm := List.mem_toFinset.mp hv
  rw [← input_list, List.mem_ofFn] at hm
  obtain ⟨i, rfl⟩ := hm
  have cut := distinguishing_ok j i
  simp only [Bool.and_eq_true, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at cut
  exact raw_required run _ _ sub (distinguishing j i) (flipped j i) cut.1
    (fun w hw ne => (cut.2 w hw).resolve_left ne)

theorem computed_live (j : Fin 3) (C : Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 9 → Bool,
      PEqualNP.MetaComplexity.circuitFun 11 C (encodedRows j x) = exactEdge x) :
    ∃ k t S, k ≤ C.size ∧ Live graph k t S ∧
      (∀ v ∈ S, v ∈ bank j) ∧ inputs.toFinset ⊆ S := by
  have output : (execute C.gates (bank j)).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro index inside
    let r : Row := ⟨index, inside⟩
    change bit r ((execute C.gates (bank j)).getD C.output zero) = bit r graph
    rw [← b_read, execute_bits _ _ _ (fun g hg => (legal g hg).1), bank_bits, graph_exact]
    exact computes (sample r)
  have availability := get_rep (execute C.gates (bank j)) C.output
  rw [output] at availability
  obtain ⟨k, t, S, bound, run, sub⟩ :=
    extract C.gates (bank j) legal graph_proper
      (availability.resolve_right fun h => h graph_proper)
  exact ⟨k, t, S, bound, run, sub, raw_in_every_root j run sub⟩

private def pin (r : Row) : Row := Fin.ofNat 512 (r.val &&& 431)

private theorem pinned_target :
    restrictRows pin (observe graph) = observe (graphGoal 431) := by
  rw [← observe_rename]
  exact congrArg observe (by decide +kernel : rename pin graph = graphGoal 431)

private theorem cost_word (s : Sig) :
    cost (observe s) = (if s == zero || s == one then 1 else 0) := by
  classical
  by_cases hz : s = zero
  · subst s
    have h : Constant (observe zero) := ⟨false, by funext r; exact bit_zero r⟩
    simp [cost, h]
  · by_cases ho : s = one
    · subst s
      have h : Constant (observe one) := ⟨true, by funext r; exact bit_one r⟩
      simp [cost, h]
    · simp [cost, observe_proper ⟨hz, ho⟩, hz, ho]

inductive CountedRun {R : Type} (goal : Wire R) : Nat → Nat → List (Wire R) → Prop
  | stop : CountedRun goal 0 0 [goal]
  | perm {k t xs zs} : xs.Perm zs → CountedRun goal k t xs → CountedRun goal k t zs
  | one {k t a rest} (save : Bool) : CountedRun goal k t (inv a :: kept save a rest) →
      CountedRun goal (k+1) (t+1) (a::rest)
  | two {k t a b rest} (op ka kb : Bool) :
      CountedRun goal k t (combine op a b :: kept ka a (kept kb b rest)) →
      CountedRun goal (k+1) t (a::b::rest)

theorem counted_restrict {R S : Type} (rows : S → R) {goal k t ws}
    (h : CountedRun goal k t ws) :
    CountedRun (restrictRows rows goal) k t (ws.map (restrictRows rows)) := by
  induction h with
  | stop => exact CountedRun.stop
  | perm p _ ih => exact CountedRun.perm (p.map _) ih
  | one save _ ih =>
    simp only [List.map_cons, restrict_kept] at ih ⊢
    exact CountedRun.one save ih
  | two op ka kb _ ih =>
    simp only [List.map_cons, restrict_kept] at ih ⊢
    cases op
    · exact CountedRun.two false ka kb ih
    · exact CountedRun.two true ka kb ih

inductive Forward {R : Type} (roots : List (Wire R)) : Nat → Nat → List (Wire R) → Prop
  | start : Forward roots 0 0 roots
  | one {b t bank a} : Forward roots b t bank → a ∈ bank →
      Forward roots b (t+1) (bank ++ [inv a])
  | two {b t bank a c} (op : Bool) : Forward roots b t bank → a ∈ bank → c ∈ bank →
      Forward roots (b+1) t (bank ++ [combine op a c])

private theorem bank_extend {R : Type} {bank : List (Wire R)} (a : Wire R) {x : Wire R}
    (h : Available bank x) : Available (bank ++ [a]) x :=
  h.elim (fun h => Or.inl (List.mem_append_left _ h)) Or.inr

private theorem cost_inv {R : Type} (a : Wire R) : cost (inv a) = cost a := by
  classical
  have iff_const : Constant (inv a) ↔ Constant a := by
    constructor
    · intro h
      have hh := inv_constant h
      have eq : inv (inv a) = a := by funext r; simp [inv]
      simpa only [eq] using hh
    · exact inv_constant
  simp [cost, iff_const]

private theorem extend_forward_one {R : Type} {roots : List (Wire R)} {p u bank a}
    (h : Forward roots p u bank) (ha : Available bank a) :
    ∃ u' bank', Forward roots p u' bank' ∧ Available bank' (inv a) ∧
      (∀ z, Available bank z → Available bank' z) ∧ u' ≤ u+1 := by
  classical
  by_cases hc : Constant a
  · exact ⟨u, bank, h, Or.inr (inv_constant hc), fun _ h => h, by omega⟩
  · refine ⟨u+1, bank ++ [inv a], Forward.one h (ha.resolve_right hc),
      Or.inl (by simp), ?_, le_rfl⟩
    intro z hz
    exact bank_extend _ hz

private theorem extend_forward_two {R : Type} {roots : List (Wire R)} {p u bank a c} (op : Bool)
    (h : Forward roots p u bank) (ha : Available bank a) (hc : Available bank c) :
    ∃ p' bank', Forward roots p' u bank' ∧ Available bank' (combine op a c) ∧
      (∀ z, Available bank z → Available bank' z) ∧
      p'+cost a+cost c ≤ p+1+cost (combine op a c) := by
  classical
  by_cases constant : Constant a ∨ Constant c
  · refine ⟨p, bank, h, from_constant op constant ha hc, fun _ h => h, ?_⟩
    by_cases ca : Constant a <;> by_cases cc : Constant c
    · simp [cost, ca, cc, both_constant op ca cc]
    · simp [cost, ca, cc]
    · simp [cost, ca, cc]
    · exact False.elim (constant.elim ca cc)
  · have na : ¬Constant a := fun h => constant (Or.inl h)
    have nc : ¬Constant c := fun h => constant (Or.inr h)
    refine ⟨p+1, bank ++ [combine op a c], Forward.two op h (ha.resolve_right na)
      (hc.resolve_right nc), Or.inl (by simp), ?_, by simp [cost, na, nc]⟩
    intro z hz
    exact bank_extend _ hz

theorem counted_contract {R : Type} {goal : Wire R} (nc : ¬ Constant goal)
    {k t ws} (h : CountedRun goal k t ws) {roots : List (Wire R)} {p u bank}
    (hp : Forward roots p u bank) (hs : supply bank ws) :
    ∃ q v next, Forward roots q v next ∧ Available next goal ∧
      q + mass ws + t ≤ p + k ∧ v ≤ u + t := by
  classical
  induction h generalizing p u bank with
  | stop =>
    exact ⟨p,u,bank,hp,hs _ (by simp),by simp [mass,cost,nc],by omega⟩
  | perm eq _ ih =>
    have hsub : supply bank _ := fun a ha => hs a (eq.mem_iff.mp ha)
    obtain ⟨q,v,next,reach,hit,lim,vlim⟩ := ih hp hsub
    exact ⟨q,v,next,reach,hit,by simpa only [mass,← (eq.map cost).sum_eq] using lim,vlim⟩
  | @one k t a rest save _ ih =>
    obtain ⟨u',W,hw,hit,inc,ul⟩ := extend_forward_one hp (hs a (by simp))
    have ht : supply W (inv a :: kept save a rest) := by
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hit
      · exact inc z (hs z (List.mem_cons.mpr (mem_kept hz)))
    obtain ⟨q,v,next,reach,out,lim,vlim⟩ := ih hw ht
    have keptMass := mass_kept a rest save
    rw [mass_cons, cost_inv] at lim
    rw [mass_cons]
    exact ⟨q,v,next,reach,out,by omega,by omega⟩
  | @two k t a c rest op ka kc _ ih =>
    obtain ⟨p',W,hw,hit,inc,lim1⟩ := extend_forward_two op hp (hs a (by simp)) (hs c (by simp))
    have ht : supply W (combine op a c :: kept ka a (kept kc c rest)) := by
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hit
      · apply inc
        apply hs
        rcases mem_kept hz with rfl | hz
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hz))
    obtain ⟨q,v,next,reach,out,lim,vlim⟩ := ih hw ht
    have kaMass := mass_kept a (kept kc c rest) ka
    have kcMass := mass_kept c rest kc
    rw [mass_cons] at lim
    rw [mass_cons,mass_cons]
    exact ⟨q,v,next,reach,out,by omega,by omega⟩

def countsBinary (g : Gate) : Bool :=
  match g.op with
  | .not => false
  | _ => true

private theorem read_index {R : Type} {bank : List (Wire R)} {a : Wire R} (h : a ∈ bank) :
    ∃ i : Nat, ∀ r : R, (bank.map fun f => f r).getD i false = a r := by
  obtain ⟨i,hi,hval⟩ := List.mem_iff_getElem.mp h
  refine ⟨i, fun r => ?_⟩
  rw [List.getD_eq_getElem _ _ (by simp [hi])]
  simpa [hval]

private theorem execute_suffix (gates : List Gate) (g : Gate) (roots : List Bool) :
    (Circuit.mk (gates ++ [g]) 0).wires roots =
      let xs := (Circuit.mk gates 0).wires roots
      xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)] := by
  simp only [Circuit.wires,List.foldl_append,List.foldl_cons,List.foldl_nil]

theorem forward_circuit {R : Type} {roots : List (Wire R)} {b u bank}
    (h : Forward roots b u bank) :
    ∃ gs : List Gate, gs.length = b+u ∧ gs.countP countsBinary = b ∧
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g.inputs.length ≤ 2) ∧
      (u = 0 → ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∀ r : R, (Circuit.mk gs 0).wires (roots.map fun a => a r) = (bank.map fun a => a r) := by
  induction h with
  | start => exact ⟨[],rfl,rfl,by simp,by simp,fun _ => rfl⟩
  | @one b u bank a _ mem ih =>
    obtain ⟨gs,len,count,legal,_,exec⟩ := ih
    obtain ⟨i,hi⟩ := read_index mem
    let g : Gate := ⟨.not,[i]⟩
    refine ⟨gs++[g], by simp [len,Nat.add_assoc], by simp [List.countP_append, count, countsBinary, g],
      ?_, by omega, ?_⟩
    · intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact legal v hv
      · obtain rfl := List.mem_singleton.mp hv
        simp [g]
    · intro r
      rw [execute_suffix,exec]
      simp only [g,GateOp.eval,List.map_append,List.map_cons,List.map_nil,List.headD_cons,inv]
      rw [hi r]
  | @two b u bank a c op _ ma mc ih =>
    obtain ⟨gs,len,count,legal,monotone,exec⟩ := ih
    obtain ⟨i,hi⟩ := read_index ma
    obtain ⟨j,hj⟩ := read_index mc
    let g : Gate := ⟨if op then .or else .and,[i,j]⟩
    have hb : countsBinary g = true := by cases op <;> rfl
    have hg : g.op = .and ∨ g.op = .or := by cases op <;> simp [g]
    refine ⟨gs++[g], by simp [len]; omega,
      by simp [List.countP_append, count, hb], ?_, ?_, ?_⟩
    · intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact legal v hv
      · obtain rfl := List.mem_singleton.mp hv
        refine ⟨?_, by simp [g]⟩
        rcases hg with hg | hg <;> simp [hg]
    · intro h0 v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact monotone h0 v hv
      · simpa [List.mem_singleton.mp hv] using hg
    · intro r
      rw [execute_suffix,exec]
      cases op <;>
        simp only [g,Bool.false_eq_true,ite_false,ite_true,GateOp.eval,List.map_append,
          List.map_cons,List.map_nil,List.all_cons,List.all_nil,List.any_cons,List.any_nil,
          id_eq,Bool.and_true,Bool.or_false,combine]
      all_goals rw [hi r,hj r]

theorem realize_forward {R : Type} {roots : List (Wire R)} {b u bank} {goal : Wire R}
    (h : Forward roots b u bank) (hit : goal ∈ bank) :
    ∃ C : Circuit, C.size = b+u ∧ C.gates.countP countsBinary = b ∧
      PEqualNP.MetaComplexity.FanInTwo C ∧
      (u = 0 → PEqualNP.MetaComplexity.Monotone2 C) ∧
      ∀ r : R, C.eval (roots.map fun a => a r) = goal r := by
  obtain ⟨gs,len,count,legal,mono,exec⟩ := forward_circuit h
  obtain ⟨i,hi⟩ := read_index hit
  refine ⟨⟨gs,i⟩,len,count,legal,?_,?_⟩
  · intro h0 g hg
    exact ⟨mono h0 g hg,(legal g hg).2⟩
  · intro r
    unfold Circuit.eval
    change ((Circuit.mk gs 0).wires _).getD i false = _
    rw [exec,hi]

theorem list_counted_run {T : Sig} {k u S} (h : Live T k u S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : CountedRun (observe T) k u (v.map observe) := by
  classical
  induction h generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact CountedRun.perm (eq.map _) CountedRun.stop
  | @unary k u U a ha fresh _ ih =>
    let rest := (U.erase a).toList
    let save := decide (a ∈ U)
    let tail := kept save a rest
    have er : rest.toFinset = U.erase a := by simp [rest]
    have hm : a ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have ht : tail.toFinset = U := by
      rw [show tail=kept save a rest by rfl,kept_fin,er]
      by_cases hh : a ∈ U <;> simp [save,hh]
    have nd := kept_nd save a rest hr hm
    have hf : neg a ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
    have progress := ih (neg a::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    rw [List.map_cons,map_kept,obs_neg] at progress
    have perm : (a::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm,hr⟩) hv
      simp [er,eqv]
    exact CountedRun.perm (perm.map _) (CountedRun.one save progress)
  | @binary k u U a b d ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change CountedRun _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact CountedRun.perm (perm.map _) (CountedRun.two d ka kb progress)




private theorem sample_column : ∀ (r : Row) (i : Fin 9), sample r i = r.val.testBit i.val := by
  decide +kernel

private def rowBits (x : Fin 9 → Bool) : BitVec 9 :=
  (BitVec.ofBoolListLE (List.ofFn x)).cast List.length_ofFn

private def rowOf (x : Fin 9 → Bool) : Row :=
  ⟨(rowBits x).toNat, (rowBits x).isLt⟩

private theorem sample_row (x : Fin 9 → Bool) : sample (rowOf x) = x := by
  funext i
  rw [sample_column]
  change (rowBits x).getLsbD i.val = x i
  simp only [rowBits, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [i.isLt]

def singleBank (j : Fin 3) : List Sig := inputs ++ [second j]

private theorem single_nodup : ∀ j : Fin 3, (singleBank j).Nodup := by
  decide +kernel

private def thetaVars : List Sig :=
  [0, 5, 7, 3, 1, 8, 2].map fun i => inputs.getD i zero

private def thetaEmbed (x : Fin 7 → Bool) (i : Fin 9) : Bool :=
  match ([some 0, some 4, some 6, some 3, none, some 1, none, some 2, some 5] :
      List (Option (Fin 7))).getD i.val none with
  | some j => x j
  | none => false

def thetaGoal (x : Fin 7 → Bool) : Bool :=
  ([(0,1),(1,2),(0,4),(1,5),(2,6),(3,5),(4,6),(6,3)] : List (Fin 7 × Fin 7)).any
    fun e => x e.1 && x e.2

private theorem theta_input (x : Fin 7 → Bool) :
    thetaVars.map (bit (rowOf (thetaEmbed x))) = List.ofFn x := by
  change [sample (rowOf (thetaEmbed x)) 0, sample (rowOf (thetaEmbed x)) 5,
    sample (rowOf (thetaEmbed x)) 7, sample (rowOf (thetaEmbed x)) 3,
    sample (rowOf (thetaEmbed x)) 1, sample (rowOf (thetaEmbed x)) 8,
    sample (rowOf (thetaEmbed x)) 2] = List.ofFn x
  rw [sample_row]
  rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem theta_target_word : ∀ x : Fin 7 → Bool,
    bit (rowOf (thetaEmbed x)) (graphGoal 431) = thetaGoal x := by
  decide +kernel

def ThetaBinaryLower : Prop :=
  ∀ C : Circuit, PEqualNP.MetaComplexity.FanInTwo C →
    PEqualNP.MetaComplexity.circuitFun 7 C = thetaGoal →
    11 ≤ C.gates.countP countsBinary

private def selectedBank (j : Fin 3) (firstUsed secondUsed : Bool) : List Sig :=
  inputs ++ (if firstUsed then [first] else []) ++ (if secondUsed then [second j] else [])

private theorem selected_mem (j : Fin 3) (f s : Bool) (w : Sig) :
    w ∈ selectedBank j f s ↔
      w ∈ inputs ∨ (f = true ∧ w = first) ∨ (s = true ∧ w = second j) := by
  cases f <;> cases s <;> simp [selectedBank, List.mem_append, or_assoc]

private theorem identify_bank (j : Fin 3) {k t S} (run : Live graph k t S)
    (sub : ∀ v ∈ S, v ∈ bank j) :
    ∃ f s : Bool, S = (selectedBank j f s).toFinset := by
  classical
  refine ⟨decide (first ∈ S), decide (second j ∈ S), ?_⟩
  ext w
  rw [List.mem_toFinset, selected_mem]
  constructor
  · intro h
    have hm := sub w h
    simp only [bank, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hm | rfl | rfl
    · exact Or.inl hm
    · exact Or.inr (Or.inl ⟨decide_eq_true h, rfl⟩)
    · exact Or.inr (Or.inr ⟨decide_eq_true h, rfl⟩)
  · rintro (h | ⟨h,rfl⟩ | ⟨h,rfl⟩)
    · exact raw_in_every_root j run sub (List.mem_toFinset.mpr h)
    · exact of_decide_eq_true h
    · exact of_decide_eq_true h

private theorem selected_nodup : ∀ (j : Fin 3) (f s : Bool), (selectedBank j f s).Nodup := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem pinned_selection_supply : ∀ (j : Fin 3) (f s : Bool),
    (selectedBank j f s).all
      (fun a => rename pin a == zero || decide (rename pin a ∈ thetaVars)) = true := by
  decide +kernel

private theorem pinned_selection_mass (j : Fin 3) (f s : Bool) :
    mass (((selectedBank j f s).map observe).map (restrictRows pin)) = 2 + if f then 1 else 0 := by
  simp only [mass, List.map_map, Function.comp_def, ← observe_rename, cost_word]
  have finite : ∀ (j : Fin 3) (f s : Bool), ((selectedBank j f s).map fun a =>
      if rename pin a == zero || rename pin a == one then 1 else 0).sum = 2 + if f then 1 else 0 := by
    decide +kernel
  exact finite j f s

private theorem selection_binary_cost (j : Fin 3) (f s : Bool) {k t : Nat}
    (lower : ThetaBinaryLower) (run : Live graph k t (selectedBank j f s).toFinset) :
    13 + (if f then 1 else 0) + t ≤ k := by
  have plan := list_counted_run run (selectedBank j f s) (selected_nodup j f s) rfl
  have projected := counted_restrict pin plan
  have nonconst : ¬ Constant (restrictRows pin (observe graph)) := by
    rw [pinned_target]
    exact observe_proper (by unfold proper; decide +kernel)
  have hs : supply (thetaVars.map observe)
      (((selectedBank j f s).map observe).map (restrictRows pin)) := by
    intro w hw
    simp only [List.map_map, Function.comp_def, ← observe_rename] at hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    have localSupport := List.all_eq_true.mp (pinned_selection_supply j f s) v hv
    rw [Bool.or_eq_true] at localSupport
    rcases localSupport with hz | hraw
    · rw [beq_iff_eq.mp hz]
      exact Or.inr ⟨false, by funext r; exact bit_zero r⟩
    · exact Or.inl (List.mem_map_of_mem (of_decide_eq_true hraw))
  obtain ⟨q, u, bank', run', hit, bound, _⟩ :=
    counted_contract nonconst projected Forward.start hs
  obtain ⟨C, _, count, legal, _, computes⟩ := realize_forward run' (hit.resolve_right nonconst)
  have computesTheta : PEqualNP.MetaComplexity.circuitFun 7 C = thetaGoal := by
    funext x
    have eq := computes (rowOf (thetaEmbed x))
    rw [List.map_map, pinned_target] at eq
    change C.eval (thetaVars.map (bit (rowOf (thetaEmbed x)))) =
      bit (rowOf (thetaEmbed x)) (graphGoal 431) at eq
    rw [theta_input, theta_target_word] at eq
    exact eq
  have floor := lower C legal computesTheta
  rw [count] at floor
  rw [pinned_selection_mass j f s] at bound
  omega

theorem remaining_monotone (j : Fin 3) {k t S}
    (lower : ThetaBinaryLower) (short : k ≤ 13) (run : Live graph k t S)
    (sub : ∀ v ∈ S, v ∈ bank j) :
    ∃ C : Circuit, C.size ≤ 13 ∧ PEqualNP.MetaComplexity.Monotone2 C ∧
      ((∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = exactEdge x) ∨
        (∀ x : Fin 9 → Bool,
          C.eval (List.ofFn x ++
            [decide (∃ i : Fin 9, (rawMask j).testBit i.val = true ∧ x i = true)]) =
              exactEdge x)) := by
  obtain ⟨f, s, rfl⟩ := identify_bank j run sub
  have floor := selection_binary_cost j f s lower run
  have hf : f = false := by
    cases f
    · rfl
    · simp at floor
      omega
  subst f
  have ht : t = 0 := by simp at floor; omega
  have plan := list_counted_run run (selectedBank j false s) (selected_nodup j false s) rfl
  have nonconst := observe_proper graph_proper
  obtain ⟨q, u, bank', run', hit, bound, ulim⟩ :=
    counted_contract nonconst plan Forward.start (fun _ h => Or.inl h)
  obtain ⟨C, size, _, _, mono, computes⟩ := realize_forward run' (hit.resolve_right nonconst)
  refine ⟨C, by omega, mono (by omega), ?_⟩
  cases s
  · left
    intro x
    have eq := computes (rowOf x)
    rw [List.map_map] at eq
    change C.eval ((selectedBank j false false).map (bit (rowOf x))) = bit (rowOf x) graph at eq
    simpa only [selectedBank, Bool.false_eq_true, ite_false, List.append_nil, ← sampled,
      graph_exact, sample_row] using eq
  · right
    intro x
    have eq := computes (rowOf x)
    rw [List.map_map] at eq
    change C.eval ((selectedBank j false true).map (bit (rowOf x))) = bit (rowOf x) graph at eq
    simpa only [selectedBank, Bool.false_eq_true, ite_false, ite_true, List.append_nil,
      List.map_append, List.map_singleton, ← sampled, second_exact, graph_exact, sample_row] using eq

end PEqualNP.Outside.L_meta_4445_aux

namespace PEqualNP.Outside.L_meta_4445_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private theorem certified_theta : ThetaBinaryLower := by
  intro D legal computes
  have count_eq :
      countsBinary = fun g : Gate => GateOp.rec true true false (fun _ => true) true g.op := by
    funext g
    obtain ⟨op, _⟩ := g
    cases op <;> rfl
  rw [count_eq]
  exact Theta.resolved D legal computes

theorem from_computing (m : Nat) (hm : m ∈ ([81, 84, 208] : List Nat)) (C : Circuit)
    (legal : FanInTwo C)
    (computes : ∀ x : Fin 9 → Bool,
      circuitFun 11 C (Fin.snoc (Fin.snoc x (x 4 || x 6))
        (decide (∃ i : Fin 9, m.testBit i.val = true ∧ x i = true))) = exactEdge x)
    (budget : C.size ≤ 13) :
    ∃ D : Circuit, D.size ≤ 13 ∧ Monotone2 D ∧
      ((∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = exactEdge x) ∨
        (∀ x : Fin 9 → Bool,
          D.eval (List.ofFn x ++ [decide (∃ i : Fin 9, m.testBit i.val = true ∧ x i = true)]) =
            exactEdge x)) := by
  have find : ∃ j : Fin 3, rawMask j = m := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  obtain ⟨j, rfl⟩ := find
  obtain ⟨k, t, S, smaller, run, sub, _⟩ := computed_live j C legal computes
  exact remaining_monotone j certified_theta (smaller.trans budget) run sub

end PEqualNP.Outside.L_meta_4445_aux

-- Pair-only adaptation of the project's checked L-meta-1484 branching argument.

namespace PEqualNP.Outside.L_meta_4445.PairBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

theorem wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem prefix_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

theorem val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    val C x i.val = x i := by
  rw [val, prefix_val _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

theorem val_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ}
    (hi : n + C.gates.length ≤ i) : val C x i = false := by
  rw [val, List.getD_eq_default _ _ (by simpa [wiresFrom_length] using hi)]

def operand {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j i : ℕ) : Bool :=
  if i < j then val C x i else false

theorem val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) {p : ℕ} {g : Gate}
    (hp : C.gates[p]? = some g) :
    val C x (n+p) = g.op.eval (g.inputs.map (operand C x (n+p))) := by
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hp
  have hsplit : C.gates = (C.gates.take p ++ [g]) ++ C.gates.drop (p+1) := by
    conv_lhs => rw [← List.take_append_drop (p+1) C.gates]
    rw [List.take_succ_eq_append_getElem hb, heq]
  let w := wiresFrom (C.gates.take p) (List.ofFn x)
  have hw : w.length = n+p := by
    simp [w, wiresFrom_length, List.length_take, Nat.min_eq_left hb.le]
  have hread (i : ℕ) : w.getD i false = operand C x (n+p) i := by
    by_cases hi : i < n+p
    · have hv : val C x i = w.getD i false := by
        unfold val
        conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
        exact prefix_val _ w i (hw.symm ▸ hi)
      simp only [operand, ite_eq_left hi, hv]
    · rw [operand, ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
  have he : (g.inputs.map fun i => w.getD i false) = g.inputs.map (operand C x (n+p)) :=
    List.map_congr_left fun i _ => hread i
  unfold val
  conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
  change (wiresFrom (C.gates.drop (p+1))
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD (n+p) false = _
  rw [prefix_val _ _ _ (by simp [hw]), ← hw, he]
  simp [hw]

def Next (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  a < b ∧ ∃ p g, C.gates[p]? = some g ∧ b = n+p ∧ a ∈ g.inputs

def Live (n : ℕ) (C : Circuit) (i : ℕ) : Prop :=
  ReflTransGen (Next n C) i C.output

def LNext (n : ℕ) (C : Circuit) (a b : ℕ) : Prop := Next n C a b ∧ Live n C b

def Trace (n : ℕ) (C : Circuit) (P : ℕ → Prop) (i j : ℕ) : Prop :=
  ReflTransGen (fun a b => P a ∧ LNext n C a b) i j

theorem next_le {n : ℕ} {C : Circuit} {a b : ℕ} (h : ReflTransGen (Next n C) a b) :
    a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans h.1.le

theorem trace_le {n : ℕ} {C : Circuit} {P : ℕ → Prop} {a b : ℕ}
    (h : Trace n C P a b) : a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans h.2.1.1.le

theorem live_before {n : ℕ} {C : Circuit} {a b : ℕ} (hn : Next n C a b) (h : Live n C b) :
    Live n C a := (ReflTransGen.single hn).trans h

theorem trace_start {n : ℕ} {C : Circuit} {P : ℕ → Prop} {a b : ℕ}
    (h : Trace n C P a b) (hb : P b) : P a := by
  rcases h.cases_head with rfl | ⟨_, hs, _⟩
  · exact hb
  · exact hs.1

theorem align {n : ℕ} {C : Circuit} {P Q : ℕ → Prop} {v b : ℕ}
    (p : Trace n C P v b)
    (unique : ∀ a j j', a < b → P a → LNext n C a j → LNext n C a j' → j = j') :
    ∀ d, Trace n C Q v d → (d < b ∧ P d) ∨ Trace n C Q b d := by
  induction p using ReflTransGen.head_induction_on with
  | refl =>
    intro d q
    exact Or.inr q
  | head hp pt ih =>
    intro d q
    have hlt := hp.2.1.1.trans_le (trace_le pt)
    rcases q.cases_head with rfl | ⟨j, hq, qt⟩
    · exact Or.inl ⟨hlt, hp.1⟩
    · have e := unique _ _ _ hlt hp.1 hp.2 hq.2
      subst j
      exact ih _ qt

theorem difference {n : ℕ} (C : Circuit) (x y : Fin n → Bool) :
    ∀ j, Live n C j → val C x j ≠ val C y j →
      ∃ i : Fin n, x i ≠ y i ∧ Trace n C (fun a => val C x a ≠ val C y a) i.val j := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hd
    by_cases hin : j < n
    · let i : Fin n := ⟨j,hin⟩
      exact ⟨i, by simpa only [← val_input C x i, ← val_input C y i] using hd, .refl⟩
    have hb : j < n+C.gates.length := by
      by_contra! he
      exact hd ((val_beyond C x he).trans (val_beyond C y he).symm)
    obtain ⟨p, hp, rfl⟩ : ∃ p, p < C.gates.length ∧ j = n+p := ⟨j-n, by omega, by omega⟩
    let g := C.gates[p]
    have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
    have hdiff : ∃ i ∈ g.inputs, i < n+p ∧ val C x i ≠ val C y i := by
      by_contra! hn
      apply hd
      rw [val_gate C x hg, val_gate C y hg]
      apply congrArg _
      apply List.map_congr_left
      intro i hi
      by_cases hj : i < n+p
      · simp [operand, hj, hn i hi hj]
      · simp [operand, hj]
    obtain ⟨a, ha, hlt, ha'⟩ := hdiff
    have hs : Next n C a (n+p) := ⟨hlt,p,g,hg,rfl,ha⟩
    obtain ⟨i, hi, hpath⟩ := ih a hlt (live_before hs hj) ha'
    exact ⟨i, hi, hpath.tail ⟨ha',hs,hj⟩⟩

end PEqualNP.Outside.L_meta_4445.PairBound


namespace PEqualNP.Outside.L_meta_4445.PairBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

variable {n : ℕ} {C : Circuit}

theorem acts_mono (hC : Monotone2 C) {x y : Fin n → Bool}
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ j, val C x j = true → val C y j = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    by_cases hin : j < n
    · let i : Fin n := ⟨j, hin⟩
      simpa only [← val_input C x i, ← val_input C y i] using hxy i (by
        simpa only [← val_input C x i] using hj)
    by_cases hgt : n + C.gates.length ≤ j
    · rw [val_beyond C x hgt] at hj
      contradiction
    obtain ⟨p, hp, rfl⟩ : ∃ p, p < C.gates.length ∧ j = n+p := ⟨j-n, by omega, by omega⟩
    let g := C.gates[p]
    have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
    have hgate := (hC g (List.mem_of_getElem? hg)).1
    have hm (a : ℕ) : operand C x (n+p) a = true → operand C y (n+p) a = true := by
      by_cases ha : a < n+p
      · simp only [operand, ite_eq_left ha]
        exact ih a ha
      · simp [operand, ha]
    rw [val_gate C x hg] at hj
    rw [val_gate C y hg]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgate
    rcases hgate with h | h
    · simp only [h, GateOp.eval, List.all_map, Function.comp_apply, id, List.all_eq_true] at hj ⊢
      exact fun a ha => hm a (hj a ha)
    · simp only [h, GateOp.eval, List.any_map, Function.comp_apply, id, List.any_eq_true] at hj ⊢
      obtain ⟨a, ha, he⟩ := hj
      exact ⟨a, ha, hm a he⟩

def point (s : Finset (Fin n)) (i : Fin n) : Bool := decide (i ∈ s)

theorem point_mono {s t : Finset (Fin n)} (h : s ⊆ t) :
    ∀ i, point s i = true → point t i = true := by
  intro i hi
  simpa only [point, decide_eq_true_eq] using h (by simpa only [point, decide_eq_true_eq] using hi)

theorem point_insert {s : Finset (Fin n)} {v u : Fin n} (h : u ≠ v) :
    point (insert v s) u = point s u := by simp [point, h]

def Carries (C : Circuit) (v : Fin n) (a : ℕ) : Prop :=
  val C (point {v}) a ≠ val C (point (∅ : Finset (Fin n))) a

theorem carries_iff (hC : Monotone2 C) {v : Fin n} {a : ℕ} :
    Carries C v a ↔
      val C (point {v}) a = true ∧ val C (point (∅ : Finset (Fin n))) a = false := by
  have hm := acts_mono hC (point_mono (Finset.empty_subset {v})) a
  unfold Carries
  cases ha : val C (point {v}) a <;>
    cases hb : val C (point (∅ : Finset (Fin n))) a <;> simp_all

theorem singleton_path {v : Fin n} {a : ℕ} (ha : Live n C a) (hd : Carries C v a) :
    Trace n C (Carries C v) v.val a := by
  obtain ⟨i, hi, hpath⟩ := difference C (point {v}) (point ∅) a ha hd
  have e : i = v := by
    by_contra h
    exact hi (by simp [point, h])
  exact e ▸ hpath

theorem influence {v : Fin n} {P : ℕ → Prop} {b j : ℕ} {x y : Fin n → Bool}
    (path : Trace n C P v.val b)
    (unique : ∀ a k k', a < b → P a → LNext n C a k → LNext n C a k' → k = k')
    (agrees : ∀ i, i ≠ v → x i = y i) (hj : Live n C j) (hd : val C x j ≠ val C y j) :
    (j < b ∧ P j) ∨ (b ≤ j ∧ val C x b ≠ val C y b) := by
  obtain ⟨i, hi, trace⟩ := difference C x y j hj hd
  have e : i = v := by
    by_contra h
    exact hi (agrees i h)
  subst i
  rcases align path unique j trace with ha | hb
  · exact Or.inl ha
  · exact Or.inr ⟨trace_le hb, trace_start hb hd⟩

noncomputable def readers (n : ℕ) (C : Circuit) (a : ℕ) : Finset ℕ :=
  open Classical in (Finset.range (n+C.gates.length)).filter (fun b => LNext n C a b)

theorem next_in_range {a b : ℕ} (h : Next n C a b) : b < n+C.gates.length := by
  obtain ⟨_,p,g,hg,rfl,_⟩ := h
  exact Nat.add_lt_add_left (List.getElem?_eq_some_iff.1 hg).1 n

theorem mem_readers {a b : ℕ} : b ∈ readers n C a ↔ LNext n C a b := by
  classical
  unfold readers
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨next_in_range h.1, h⟩⟩

def Branch (n : ℕ) (C : Circuit) (a : ℕ) : Prop := 2 ≤ (readers n C a).card

theorem nonbranch_unique {a j j' : ℕ} (h : ¬ Branch n C a)
    (hj : LNext n C a j) (hj' : LNext n C a j') : j = j' := by
  apply Finset.card_le_one_iff.1 (show (readers n C a).card ≤ 1 from by
    unfold Branch at h; omega) (mem_readers.2 hj) (mem_readers.2 hj')

def Eligible (C : Circuit) (v : Fin n) : Prop := ∃ b, Live n C b ∧ Carries C v b ∧ Branch n C b

noncomputable def firstBranch (C : Circuit) (v : Fin n) (h : Eligible C v) : ℕ := by
  classical exact Nat.find h

theorem firstBranch_spec (v : Fin n) (h : Eligible C v) :
    Live n C (firstBranch C v h) ∧ Carries C v (firstBranch C v h) ∧ Branch n C (firstBranch C v h) := by
  classical exact Nat.find_spec h

theorem firstBranch_unique (v : Fin n) (h : Eligible C v) :
    ∀ a j j', a < firstBranch C v h → Carries C v a → LNext n C a j → LNext n C a j' → j = j' := by
  classical
  intro a j j' hl hc hj hj'
  apply nonbranch_unique _ hj hj'
  intro hb
  exact (Nat.not_le_of_gt hl) (Nat.find_min' h ⟨live_before hj.1 hj.2,hc,hb⟩)

theorem no_eligible_unique {v : Fin n} (h : ¬ Eligible C v) :
    ∀ a j j', Carries C v a → LNext n C a j → LNext n C a j' → j = j' := by
  intro a j j' hc hj hj'
  exact nonbranch_unique (fun hb => h ⟨a,live_before hj.1 hj.2,hc,hb⟩) hj hj'

end PEqualNP.Outside.L_meta_4445.PairBound


namespace PEqualNP.Outside.L_meta_4445.PairBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}

def GraphEval (C : Circuit) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ v w : Fin n, val C (point {v,w}) C.output = true ↔ G.Adj v w

theorem point_pair (he : GraphEval C G) (v w : Fin n) :
    val C (point {v,w}) C.output = true ↔ G.Adj v w :=
  he v w

theorem point_pair_quiet (he : GraphEval C G) {v w : Fin n} (hn : ¬ G.Adj v w) :
    val C (point {v,w}) C.output = false := by
  rw [← Bool.not_eq_true, point_pair he]
  exact hn

theorem point_single_quiet (he : GraphEval C G) (v : Fin n) :
    val C (point {v}) C.output = false := by
  simpa using point_pair_quiet he (G.irrefl (v := v))

theorem edge_at_output (he : GraphEval C G) {v w : Fin n} (hvw : G.Adj v w) :
    n ≤ C.output ∧ C.output < n+C.gates.length := by
  have hp := (point_pair he v w).2 hvw
  constructor
  · by_contra! hl
    let i : Fin n := ⟨C.output,hl⟩
    have hv := point_single_quiet he i
    rw [show C.output = i.val from rfl,val_input] at hv
    simp [point] at hv
  · by_contra! hgt
    rw [val_beyond C _ hgt] at hp
    contradiction

theorem two_inputs {l : List ℕ} {a b : ℕ} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b)
    (hl : l.length ≤ 2) :
    ∀ i ∈ l, i = a ∨ i = b := by
  have hsub : ({a,b} : Finset ℕ) ⊆ l.toFinset := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact List.mem_toFinset.mpr ha
    · exact List.mem_toFinset.mpr hb
  have hcard : l.toFinset.card ≤ ({a,b} : Finset ℕ).card := by
    simpa [hne] using l.toFinset_card_le.trans hl
  have hEq := Finset.eq_of_subset_of_card_le hsub hcard
  intro i hi
  have hm : i ∈ ({a,b} : Finset ℕ) := hEq.symm ▸ (List.mem_toFinset.mpr hi)
  simpa using hm

theorem carries_separate (hC : Monotone2 C) {v w : Fin n} {a : ℕ}
    (h1 : val C (point {v}) a = true) (h0 : val C (point {w}) a = false) :
    Carries C v a ∧ ¬ Carries C w a := by
  have hb : val C (point (∅ : Finset (Fin n))) a = false := by
    rw [← Bool.not_eq_true]
    intro hc
    have hh := acts_mono hC (point_mono (Finset.empty_subset {w})) a hc
    rw [h0] at hh
    contradiction
  rw [carries_iff hC,carries_iff hC]
  simp [h1,h0,hb]

theorem meeting_gate (hC : Monotone2 C) (he : GraphEval C G) {v w : Fin n}
    (hvw : G.Adj v w) :
    ∃ p g a b, C.gates[p]? = some g ∧ g.op = GateOp.and ∧ Live n C (n+p) ∧
      LNext n C a (n+p) ∧ LNext n C b (n+p) ∧
      Carries C v a ∧ ¬ Carries C w a ∧ Carries C w b ∧ ¬ Carries C v b ∧
      (∀ i ∈ g.inputs, i = a ∨ i = b) := by
  classical
  let P (i : ℕ) := Live n C i ∧ val C (point {v,w}) i = true ∧
    val C (point {v}) i = false ∧ val C (point {w}) i = false
  have hex : ∃ i, P i :=
    ⟨C.output, .refl, (point_pair he v w).2 hvw, point_single_quiet he v, point_single_quiet he w⟩
  let j := Nat.find hex
  have hj : P j := Nat.find_spec hex
  have earlier (i : ℕ) (hlt : i < j) (hl : Live n C i)
      (htrue : val C (point {v,w}) i = true) :
      val C (point {v}) i = true ∨ val C (point {w}) i = true := by
    by_contra! h
    have h' : P i := ⟨hl, htrue, by simpa using h.1, by simpa using h.2⟩
    exact (Nat.not_le_of_gt hlt) (Nat.find_min' hex h')
  have hge : n ≤ j := by
    by_contra! hh
    let i : Fin n := ⟨j,hh⟩
    obtain ⟨_,ht,hv,hw⟩ := hj
    rw [show j = i.val from rfl,val_input] at ht hv hw
    simp only [point,decide_eq_true_eq,Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with h | h
    · simp [point,h] at hv
    · simp [point,h] at hw
  have hlt : j < n+C.gates.length := by
    by_contra! hh
    have ht := hj.2.1
    rw [val_beyond C _ hh] at ht
    contradiction
  let p := j-n
  have hp : p < C.gates.length := by dsimp [p]; omega
  have ep : n+p = j := by dsimp [p]; omega
  let g := C.gates[p]
  have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp,rfl⟩
  have hl := hC g (List.mem_of_getElem? hg)
  have hh : Live n C (n+p) := ep ▸ hj.1
  have hs1 : val C (point {v,w}) (n+p) = true := ep ▸ hj.2.1
  have hs2 : val C (point {v}) (n+p) = false := ep ▸ hj.2.2.1
  have hs3 : val C (point {w}) (n+p) = false := ep ▸ hj.2.2.2
  have reads (i : ℕ) (hi : i < n+p) (hm : i ∈ g.inputs) : LNext n C i (n+p) :=
    ⟨⟨hi,p,g,hg,rfl,hm⟩,hh⟩
  have hAnd : g.op = GateOp.and := by
    rcases hl.1 with h | h
    · exact h
    have hop : g.op = GateOp.or := h
    simp only [val_gate C _ hg, hop, GateOp.eval, List.any_map, Function.comp_apply, id,
      List.any_eq_true] at hs1
    obtain ⟨i,hi,ht⟩ := hs1
    have hi' : i < n+p := by
      by_contra hh'
      simp [operand,hh'] at ht
    have ht' : val C (point {v,w}) i = true := by simpa [operand,hi'] using ht
    rcases earlier i (ep ▸ hi') (live_before (reads i hi' hi).1 hh) ht' with hV | hW
    · have hs := hs2
      rw [← Bool.not_eq_true, val_gate C _ hg,hop,GateOp.eval,List.any_map,List.any_eq_true] at hs
      exact (hs ⟨i,hi,by simpa [operand,hi'] using hV⟩).elim
    · have hs := hs3
      rw [← Bool.not_eq_true, val_gate C _ hg,hop,GateOp.eval,List.any_map,List.any_eq_true] at hs
      exact (hs ⟨i,hi,by simpa [operand,hi'] using hW⟩).elim
  have hAll : ∀ i ∈ g.inputs, operand C (point {v,w}) (n+p) i = true := by
    simpa [val_gate C _ hg,hAnd,GateOp.eval,List.all_eq_true] using hs1
  have hFalse (x : Fin n → Bool) (hX : val C x (n+p) = false) :
      ∃ i ∈ g.inputs, operand C x (n+p) i = false := by
    by_contra! h
    have ht : val C x (n+p) = true := by
      rw [val_gate C _ hg,hAnd,GateOp.eval,List.all_map,List.all_eq_true]
      intro i hi
      simpa using h i hi
    rw [hX] at ht
    contradiction
  obtain ⟨a,ha,hwa⟩ := hFalse _ hs3
  obtain ⟨b,hb,hvb⟩ := hFalse _ hs2
  have before (i : ℕ) (h : i ∈ g.inputs) : i < n+p := by
    by_contra hi
    have hX := hAll i h
    simp [operand,hi] at hX
  have ha' := before a ha
  have hb' := before b hb
  rw [operand,ite_eq_left ha'] at hwa
  rw [operand,ite_eq_left hb'] at hvb
  have near (i : ℕ) (h : i ∈ g.inputs) :
      val C (point {v}) i = true ∨ val C (point {w}) i = true := by
    have hi := before i h
    apply earlier i (ep ▸ hi) (live_before (reads i hi h).1 hh)
    simpa [operand,hi] using hAll i h
  have hva := (near a ha).resolve_right (by rw [hwa]; decide)
  have hwb := (near b hb).resolve_left (by rw [hvb]; decide)
  have hne : a ≠ b := fun e => Bool.noConfusion (hva.symm.trans (e ▸ hvb))
  exact ⟨p,g,a,b,hg,hAnd,hh,reads a ha' ha,reads b hb' hb,
    (carries_separate hC hva hwa).1,(carries_separate hC hva hwa).2,
    (carries_separate hC hwb hvb).1,(carries_separate hC hwb hvb).2,
    two_inputs ha hb hne hl.2⟩

theorem covers_edge (hC : Monotone2 C) (he : GraphEval C G) {v w a₀ b₀ : Fin n}
    (hvw : G.Adj v w) (ha₀ : G.Adj v a₀) (_ha₁ : a₀ ≠ w)
    (hb₀ : G.Adj w b₀) (_hb₁ : b₀ ≠ v) (hind : a₀ = b₀ ∨ ¬ G.Adj a₀ b₀) :
    Eligible C v ∨ Eligible C w := by
  by_contra! bad
  obtain ⟨p,g,a,b,hg,hAnd,hj,ha,hb,hva,hwa,hwb,hvb,hs⟩ := meeting_gate hC he hvw
  have pathV : Trace n C (Carries C v) v.val (n+p) :=
    (singleton_path (live_before ha.1 ha.2) hva).tail ⟨hva,ha⟩
  have pathW : Trace n C (Carries C w) w.val (n+p) :=
    (singleton_path (live_before hb.1 hb.2) hwb).tail ⟨hwb,hb⟩
  have uniqueV : ∀ k j j', k < n+p → Carries C v k → LNext n C k j → LNext n C k j' → j=j' :=
    fun k j j' _ => no_eligible_unique bad.1 k j j'
  have uniqueW : ∀ k j j', k < n+p → Carries C w k → LNext n C k j → LNext n C k j' → j=j' :=
    fun k j j' _ => no_eligible_unique bad.2 k j j'
  let S : Finset (Fin n) := {a₀,b₀}
  let x := point S
  let y := point (insert v S)
  let z := point (insert w S)
  have hzero : val C x C.output = false :=
    point_pair_quiet he (hind.elim (fun e => e ▸ G.irrefl (v := a₀)) id)
  have subY : ({v,a₀} : Finset (Fin n)) ⊆ insert v S := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp [S]
  have subZ : ({w,b₀} : Finset (Fin n)) ⊆ insert w S := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp [S]
  have hY : val C y C.output = true :=
    acts_mono hC (point_mono subY) C.output ((point_pair he v a₀).2 ha₀)
  have hZ : val C z C.output = true :=
    acts_mono hC (point_mono subZ) C.output ((point_pair he w b₀).2 hb₀)
  have jout := next_le hj
  have hvj := influence pathV uniqueV (fun _ hi => (point_insert hi).symm) ReflTransGen.refl (show val C x C.output ≠ val C y C.output from by rw [hzero,hY]; decide)
  have hwj := influence pathW uniqueW (fun _ hi => (point_insert hi).symm) ReflTransGen.refl (show val C x C.output ≠ val C z C.output from by rw [hzero,hZ]; decide)
  have hdiffV := (hvj.resolve_left (fun h => (Nat.not_lt_of_ge jout) h.1)).2
  have hdiffW := (hwj.resolve_left (fun h => (Nat.not_lt_of_ge jout) h.1)).2
  have hX : val C x (n+p) = false := by
    rw [← Bool.not_eq_true]
    intro htrue
    exact hdiffV (htrue.trans (acts_mono hC (point_mono (Finset.subset_insert _ _)) _ htrue).symm)
  have hyj : val C y (n+p) = true := by
    rw [hX] at hdiffV
    simpa using hdiffV.symm
  have hzj : val C z (n+p) = true := by
    rw [hX] at hdiffW
    simpa using hdiffW.symm
  have hAX : val C x a = val C z a := by
    by_contra h
    rcases influence pathW uniqueW (fun _ hi => (point_insert hi).symm) (live_before ha.1 ha.2) h with h' | h'
    · exact hwa h'.2
    · exact (Nat.not_le_of_gt ha.1.1) h'.1
  have hBX : val C x b = val C y b := by
    by_contra h
    rcases influence pathV uniqueV (fun _ hi => (point_insert hi).symm) (live_before hb.1 hb.2) h with h' | h'
    · exact hvb h'.2
    · exact (Nat.not_le_of_gt hb.1.1) h'.1
  have hYall : ∀ i ∈ g.inputs, operand C y (n+p) i = true := by
    simpa [val_gate C _ hg,hAnd,GateOp.eval,List.all_eq_true] using hyj
  have hZall : ∀ i ∈ g.inputs, operand C z (n+p) i = true := by
    simpa [val_gate C _ hg,hAnd,GateOp.eval,List.all_eq_true] using hzj
  have hin (i : ℕ) : LNext n C i (n+p) → i ∈ g.inputs := by
    rintro ⟨⟨_,k,g',he',hk,hmem⟩,_⟩
    have e : k=p := by omega
    subst k
    rw [hg] at he'
    cases he'
    exact hmem
  have hxA := hZall a (hin a ha)
  have hxB := hYall b (hin b hb)
  rw [operand,ite_eq_left ha.1.1,← hAX] at hxA
  rw [operand,ite_eq_left hb.1.1,← hBX] at hxB
  have hs' : val C x (n+p) = true := by
    rw [val_gate C _ hg,hAnd,GateOp.eval,List.all_map,List.all_eq_true]
    intro i hi
    rcases hs i hi with rfl | rfl
    · simpa [Function.comp_apply,operand,ha.1.1] using hxA
    · simpa [Function.comp_apply,operand,hb.1.1] using hxB
  rw [hX] at hs'
  contradiction

end PEqualNP.Outside.L_meta_4445.PairBound


namespace PEqualNP.Outside.L_meta_4445.PairBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}

theorem value_at_branch {v : Fin n} {x y : Fin n → Bool} (hv : Eligible C v)
    (agrees : ∀ i, i ≠ v → x i = y i)
    (hb : val C x (firstBranch C v hv) = val C y (firstBranch C v hv)) :
    val C x C.output = val C y C.output := by
  by_contra h
  have spec := firstBranch_spec v hv
  have path := singleton_path spec.1 spec.2.1
  rcases influence path (firstBranch_unique v hv) agrees ReflTransGen.refl h with bad | bad
  · exact (Nat.not_lt_of_ge (next_le spec.1)) bad.1
  · exact bad.2 hb

theorem branch_injective (hC : Monotone2 C) (he : GraphEval C G)
    (htwins : ∀ v w : Fin n, v ≠ w → ¬ G.Adj v w → 2 ≤ (G.neighborSet v).ncard →
      2 ≤ (G.neighborSet w).ncard → ∃ u : Fin n, ¬ (G.Adj v u ↔ G.Adj w u))
    {v w : Fin n} (hv : Eligible C v) (hw : Eligible C w)
    (hdv : 2 ≤ (G.neighborSet v).ncard) (hdw : 2 ≤ (G.neighborSet w).ncard)
    (h : firstBranch C v hv = firstBranch C w hw) : v = w := by
  classical
  by_contra hne
  let b := firstBranch C v hv
  have hw_b : firstBranch C w hw = b := h.symm
  have hvtrue : val C (point {v}) b = true :=
    (carries_iff hC).1 (firstBranch_spec v hv).2.1 |>.1
  have hwtrue : val C (point {w}) b = true := by
    rw [← hw_b]
    exact (carries_iff hC).1 (firstBranch_spec w hw).2.1 |>.1
  by_cases hadj : G.Adj v w
  · have hbig : val C (point (insert w ({v} : Finset (Fin n)))) b = true :=
      acts_mono hC (point_mono (Finset.subset_insert _ _)) b hvtrue
    have eq := value_at_branch hw
      (x := point {v}) (y := point (insert w ({v} : Finset (Fin n))))
      (fun _ hi => (point_insert hi).symm) (by rw [hw_b,hvtrue,hbig])
    have hy : val C (point (insert w ({v} : Finset (Fin n)))) C.output = true :=
      (point_pair he w v).2 (G.adj_symm hadj)
    rw [point_single_quiet he v,hy] at eq
    contradiction
  obtain ⟨u,hu⟩ := htwins v w hne hadj hdv hdw
  have hx : val C (point {v,u}) b = true := acts_mono hC
    (point_mono (by simp)) b hvtrue
  have hy : val C (point {w,u}) b = true := acts_mono hC
    (point_mono (by simp)) b hwtrue
  have hxyz : val C (point (insert w ({v,u} : Finset (Fin n)))) b = true :=
    acts_mono hC (point_mono (Finset.subset_insert _ _)) b hx
  have hEq : (insert w ({v,u} : Finset (Fin n))) = insert v {w,u} :=
    Finset.insert_comm _ _ _
  have e1 := value_at_branch hw
    (x := point {v,u}) (y := point (insert w ({v,u} : Finset (Fin n))))
    (fun _ hi => (point_insert hi).symm) (by rw [hw_b,hx,hxyz])
  have e2 := value_at_branch hv
    (x := point {w,u}) (y := point (insert v ({w,u} : Finset (Fin n))))
    (fun _ hi => (point_insert hi).symm) (by rw [← hEq]; exact hy.trans hxyz.symm)
  have e : val C (point {v,u}) C.output = val C (point {w,u}) C.output :=
    e1.trans (by rw [hEq,e2])
  apply hu
  rw [← point_pair he v u, ← point_pair he w u, e]

noncomputable def living (n : ℕ) (C : Circuit) : Finset ℕ :=
  open Classical in (Finset.range (n+C.gates.length)).filter (Live n C)

theorem mem_living {w : ℕ} : w ∈ living n C ↔ w < n+C.gates.length ∧ Live n C w := by
  classical
  simp [living]

theorem input_live (he : GraphEval C G) {v u : Fin n} (hvu : G.Adj v u) :
    Live n C v.val := by
  have hx : val C (point {u}) C.output = false := point_single_quiet he u
  have hy : val C (point {v,u}) C.output = true := (point_pair he v u).2 hvu
  obtain ⟨i,hi,trace⟩ := difference C (point {u}) (point {v,u}) C.output ReflTransGen.refl
    (by rw [hx,hy]; decide)
  have ei : i=v := by
    by_contra h
    exact hi ((point_insert h).symm)
  subst i
  rcases trace.cases_head with h | ⟨b,hb,_⟩
  · rw [h]
    exact .refl
  · exact live_before hb.2.1 hb.2.2

theorem live_readers_nonempty {a : ℕ} (ha : Live n C a) (hneq : a ≠ C.output) :
    (readers n C a).Nonempty := by
  rcases ha.cases_head with h | ⟨b,hb,hpath⟩
  · exact (hneq h).elim
  · exact ⟨b,mem_readers.2 ⟨hb,hpath⟩⟩

theorem readers_filter (a : ℕ) :
    open Classical in readers n C a = (living n C).filter (fun b => LNext n C a b) := by
  classical
  ext b
  simp only [mem_readers,Finset.mem_filter,mem_living]
  exact ⟨fun h => ⟨⟨next_in_range h.1,h.2⟩,h⟩, And.right⟩

theorem incoming_bound {j : ℕ} (hC : Monotone2 C) (hj : j ∈ living n C) :
    open Classical in ((living n C).filter fun i => LNext n C i j).card ≤ if j<n then 0 else 2 := by
  classical
  by_cases hi : j < n
  · rw [ite_eq_left hi]
    apply Nat.le_of_eq
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.2
    intro i hm
    obtain ⟨_,⟨_,p,g,hg,hp,_⟩,_⟩ := Finset.mem_filter.mp hm
    omega
  rw [ite_eq_right hi]
  have hj' := (mem_living.1 hj).1
  let p := j-n
  have hp : p < C.gates.length := by dsimp [p]; omega
  have he : j=n+p := by dsimp [p]; omega
  let g := C.gates[p]
  have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp,rfl⟩
  have hsub : ((living n C).filter fun i => LNext n C i j) ⊆ g.inputs.toFinset := by
    intro a ha
    obtain ⟨_,⟨_,q,g',hg',hq,hm⟩,_⟩ := Finset.mem_filter.1 ha
    have ep : p=q := by omega
    subst q
    rw [hg] at hg'
    cases hg'
    exact List.mem_toFinset.2 hm
  exact (Finset.card_le_card hsub).trans (g.inputs.toFinset_card_le.trans
    (hC g (List.mem_of_getElem? hg)).2)

theorem branch_budget (hC : Monotone2 C) (he : GraphEval C G)
    (hdegree : ∀ v : Fin n, ∃ u, G.Adj v u) (ho : C.output ∈ living n C) :
    open Classical in n + ((living n C).filter (Branch n C)).card ≤ C.size + 1 := by
  classical
  let W := living n C
  let S := W.filter (fun a => ¬ a < n)
  let B := W.filter (Branch n C)
  let R := W.erase C.output
  have hSub : Finset.range n ⊆ W := by
    intro a ha
    have hi := Finset.mem_range.1 ha
    let v : Fin n := ⟨a,hi⟩
    obtain ⟨u,hu⟩ := hdegree v
    exact mem_living.2 ⟨by omega,input_live he hu⟩
  have hW : W.card = n + S.card := by
    have h := Finset.card_sdiff_add_card_eq_card hSub
    have e : W \ Finset.range n = S := by ext a; simp [S]
    rw [e,Finset.card_range] at h
    omega
  have hR : R.card + 1 = W.card := by
    dsimp [R]
    have h := Finset.card_erase_add_one ho
    exact h
  have hS : S.card ≤ C.gates.length := by
    rw [show C.gates.length = (Finset.range C.gates.length).card by simp]
    apply Finset.card_le_card_of_injOn (fun a => a-n)
    · intro a ha
      have h : a < n+C.gates.length := (mem_living.1 (Finset.mem_filter.1 ha).1).1
      have h0 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
      apply Finset.mem_range.2
      change a-n < C.gates.length
      omega
    · intro a ha b hb hab
      have h1 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
      have h2 : n ≤ b := Nat.le_of_not_gt (Finset.mem_filter.1 hb).2
      change a-n=b-n at hab
      omega
  have hoNone : ¬ Branch n C C.output := by
    intro h
    have hgt : 0 < (readers n C C.output).card := by unfold Branch at h; omega
    obtain ⟨b,hb⟩ := Finset.card_pos.1 hgt
    have hs := mem_readers.1 hb
    exact (Nat.not_lt_of_ge (next_le hs.2)) hs.1.1
  have hlow : R.card+B.card ≤ ∑ a ∈ W, (readers n C a).card := by
    have eR : (∑ a ∈ W, (if a=C.output then 0 else 1 : ℕ)) = R.card := by
      calc
        _ = ∑ a ∈ W, (if a≠C.output then 1 else 0 : ℕ) := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases h : a=C.output <;> simp [h]
        _ = R.card := by rw [← Finset.sum_filter]; simp [R,Finset.filter_ne']
    have eB : (∑ a ∈ W, (if Branch n C a then 1 else 0 : ℕ)) = B.card := by
      rw [← Finset.sum_filter]
      simp [B]
    rw [← eR,← eB,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a ha
    have hl := (mem_living.1 ha).2
    by_cases heq : a=C.output
    · subst a
      simp [hoNone]
    · by_cases hb : Branch n C a
      · have hb' : 2 ≤ (readers n C a).card := hb
        simpa [heq,hb] using hb'
      · simpa [heq,hb] using Nat.succ_le_of_lt (Finset.card_pos.2 (live_readers_nonempty hl heq))
  have hcomm :
      (∑ a ∈ W, (readers n C a).card) =
        ∑ j ∈ W, (W.filter fun a => LNext n C a j).card := by
    simp_rw [readers_filter,Finset.card_eq_sum_ones,Finset.sum_filter]
    exact Finset.sum_comm
  have hupp : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) ≤ 2*S.card := by
    have H : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) ≤
        ∑ j ∈ W, (if j<n then 0 else 2 : ℕ) :=
      Finset.sum_le_sum fun j hj => incoming_bound hC hj
    have e : (∑ j ∈ W, (if j<n then 0 else 2 : ℕ)) = 2*S.card := by
      simp [S,Finset.sum_ite, Nat.mul_comm]
    exact H.trans_eq e
  rw [hcomm] at hlow
  change n+B.card ≤ C.gates.length+1
  omega

end PEqualNP.Outside.L_meta_4445.PairBound


namespace PEqualNP.Outside.L_meta_4445.PairBound

theorem step614 :
    ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ v : Fin n, ∃ w : Fin n, G.Adj v w) → (∀ v w : Fin n, v ≠ w → ¬ G.Adj v w → 2 ≤ (G.neighborSet v).ncard → 2 ≤ (G.neighborSet w).ncard → ∃ u : Fin n, ¬ (G.Adj v u ↔ G.Adj w u)) → (∀ v w : Fin n, G.Adj v w → 2 ≤ (G.neighborSet v).ncard → 2 ≤ (G.neighborSet w).ncard → ∃ a b : Fin n, G.Adj v a ∧ a ≠ w ∧ G.Adj w b ∧ b ≠ v ∧ (a = b ∨ ¬ G.Adj a b)) → (∃ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → 2 ≤ (G.neighborSet u).ncard → 2 ≤ (G.neighborSet v).ncard → u ∈ S ∨ v ∈ S) ∧ S.card = t) → (∀ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → 2 ≤ (G.neighborSet u).ncard → 2 ≤ (G.neighborSet v).ncard → u ∈ S ∨ v ∈ S) → t ≤ S.card) → PEqualNP.MetaComplexity.Monotone2 C → (∀ v w : Fin n, C.eval (List.ofFn (point {v,w})) = true ↔ G.Adj v w) → n + t ≤ C.size + 1 := by
  open PEqualNP.Outside.L_meta_4445.PairBound in
  classical
  intro n t G C hdegree htwins hadj _ ht hC he
  by_cases hn : n=0
  · subst n
    have ht0 := ht ∅ (fun u => Fin.elim0 u)
    simp at ht0
    omega
  have hE : GraphEval C G := he
  let v : Fin n := ⟨0, by omega⟩
  obtain ⟨w, hve⟩ := hdegree v
  have ho := (edge_at_output hE hve).2
  have ho' : C.output ∈ living n C := mem_living.2 ⟨ho, Relation.ReflTransGen.refl⟩
  let S : Finset (Fin n) := Finset.univ.filter fun v =>
    2 ≤ (G.neighborSet v).ncard ∧ Eligible C v
  have hS (u : Fin n) : u ∈ S ↔ 2 ≤ (G.neighborSet u).ncard ∧ Eligible C u := by
    simp [S]
  have htc : t ≤ S.card := by
    apply ht S
    intro a b hab hda hdb
    obtain ⟨u,v,hu,hu',hv,hv',hind⟩ := hadj a b hab hda hdb
    rcases covers_edge hC hE hab hu hu' hv hv' hind with ha | hb
    · exact Or.inl ((hS a).2 ⟨hda,ha⟩)
    · exact Or.inr ((hS b).2 ⟨hdb,hb⟩)
  let B := (living n C).filter (Branch n C)
  let f (u : Fin n) := if h : Eligible C u then firstBranch C u h else 0
  have hf (u : Fin n) (hu : Eligible C u) : f u = firstBranch C u hu := by simp [f,hu]
  have hcap : S.card ≤ B.card := by
    apply Finset.card_le_card_of_injOn f
    · intro u hu
      obtain ⟨_,hs⟩ := (hS u).1 hu
      have hb := firstBranch_spec u hs
      have hlt := (next_le hb.1).trans_lt ho
      show f u ∈ B
      rw [hf u hs]
      exact Finset.mem_filter.2 ⟨mem_living.2 ⟨hlt,hb.1⟩,hb.2.2⟩
    · intro u hu v hv huv
      obtain ⟨hdu,hsu⟩ := (hS u).1 hu
      obtain ⟨hdv,hsv⟩ := (hS v).1 hv
      rw [hf u hsu,hf v hsv] at huv
      exact branch_injective hC hE htwins hsu hsv hdu hdv huv
  have hbudget := branch_budget hC hE hdegree ho'
  exact (Nat.add_le_add_left (htc.trans hcap) n).trans hbudget

end PEqualNP.Outside.L_meta_4445.PairBound


namespace PEqualNP.Outside.L_meta_4445.PairBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edgeList (b : Bool) : List (Fin 9 × Fin 9) :=
  (if b then [(1,3)] else []) ++
    [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]

def graph (b : Bool) : SimpleGraph (Fin 9) :=
  SimpleGraph.fromRel (fun i j => (i,j) ∈ edgeList b)

private abbrev adj (b : Bool) (i j : Fin 9) : Prop :=
  i ≠ j ∧ ((i,j) ∈ edgeList b ∨ (j,i) ∈ edgeList b)

private theorem noIsolates : ∀ b i, ∃ j, adj b i j := by
  decide +kernel

set_option synthInstance.maxSize 10000 in
private theorem distinctNeighborhoods :
    ∀ b i j, i ≠ j → ¬ adj b i j → ∃ k, ¬ (adj b i k ↔ adj b j k) := by
  decide +kernel

set_option synthInstance.maxSize 10000 in
private theorem edgeWitness :
    ∀ b i j, adj b i j → ∃ a c, adj b i a ∧ a ≠ j ∧ adj b j c ∧ c ≠ i ∧
      (a = c ∨ ¬ adj b a c) := by
  decide +kernel

private theorem degreeCheck (b : Bool) (i : Fin 9) :
    2 ≤ (Finset.univ.filter (adj b i)).card := by
  revert i b
  decide +kernel

private theorem twoNeighbors (b : Bool) (i : Fin 9) :
    2 ≤ ((graph b).neighborSet i).ncard := by
  let _ : DecidableRel (graph b).Adj := fun j k =>
    inferInstanceAs (Decidable (adj b j k))
  rw [SimpleGraph.ncard_neighborSet, SimpleGraph.degree]
  have same : (graph b).neighborFinset i = Finset.univ.filter (adj b i) := by
    ext j
    rw [SimpleGraph.mem_neighborFinset, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    rfl
  rw [same]
  exact degreeCheck b i

private theorem coverExample : ∀ b i j, adj b i j →
    i ∈ ({0,1,3,7,8} : Finset (Fin 9)) ∨ j ∈ ({0,1,3,7,8} : Finset (Fin 9)) := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
private theorem coverLower : ∀ b (S : Finset (Fin 9)),
    (∀ i j, adj b i j → i ∈ S ∨ j ∈ S) → 5 ≤ S.card := by
  decide +kernel

theorem lower (b : Bool) (C : Circuit) (hm : Monotone2 C)
    (h : ∀ v w : Fin 9, C.eval (List.ofFn (point {v,w})) = true ↔ (graph b).Adj v w) :
    13 ≤ C.size := by
  have lb := step614 9 5 (graph b) C
    (noIsolates b)
    (fun u v huv hnot _ _ => distinctNeighborhoods b u v huv hnot)
    (fun u v huv _ _ => edgeWitness b u v huv)
    ⟨{0,1,3,7,8}, (fun u v huv _ _ => coverExample b u v huv), by decide⟩
    (fun S hS => coverLower b S (fun u v huv =>
      hS u v huv (twoNeighbors b u) (twoNeighbors b v)))
    hm h
  omega

end PEqualNP.Outside.L_meta_4445.PairBound

namespace PEqualNP.Outside.L_meta_4445.PairSemantics

def target (x : Fin 9 → Bool) : Bool :=
  ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any
    fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))

def support (u v : Fin 9) : Fin 9 → Bool :=
  fun i => decide (i = u ∨ i = v)

def supportWith (u v r : Fin 9) : Fin 9 → Bool :=
  fun i => decide ((i = u ∨ i = v) ∨ i = r)

def chord (u v : Fin 9) : Bool :=
  decide ((u = 1 ∧ v = 3) ∨ (u = 3 ∧ v = 1))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem hasZeroExtension :
    ∀ t u v : Fin 9, (t = 0 ∨ t = 2 ∨ t = 7) →
      target (support u v) = false → chord u v = false →
      ∃ r : Fin 9, (r = 4 ∨ r = 6 ∨ r = t) ∧ target (supportWith u v r) = false := by
  decide +kernel

theorem support_le (u v r : Fin 9) : support u v ≤ supportWith u v r := by
  intro i
  unfold support supportWith
  by_cases h : i = u ∨ i = v
  · simp [h]
  · simp [h]

theorem support_finset (u v : Fin 9) :
    support u v = (fun i => decide (i ∈ ({u,v} : Finset (Fin 9)))) := by
  funext i
  simp [support]

theorem support_swap (u v : Fin 9) : support u v = support v u := by
  funext i
  simp only [support, or_comm]

theorem agrees (K : (Fin 9 → Bool) → Bool) (t : Fin 9)
    (ht : t = 0 ∨ t = 2 ∨ t = 7) (mono : Monotone K)
    (positive : ∀ x, target x = true → K x = true)
    (wired : ∀ x, (x 4 || x 6 || x t) = true → K x = target x) :
    ∃ b : Bool, ∀ u v : Fin 9, K (support u v) =
      (target (support u v) || (b && chord u v)) := by
  refine ⟨K (support 1 3), fun u v => ?_⟩
  cases he : target (support u v)
  · cases hc : chord u v
    · obtain ⟨r, hr, htarget⟩ := hasZeroExtension t u v ht he hc
      have active : (supportWith u v r 4 || supportWith u v r 6 || supportWith u v r t) = true := by
        rcases hr with rfl | rfl | rfl <;> simp [supportWith]
      have hz : K (supportWith u v r) = false := (wired _ active).trans htarget
      have le := mono (support_le u v r)
      rw [hz] at le
      have falseBound : ∀ c : Bool, c ≤ false → c = false := by decide
      simpa only [Bool.and_false, Bool.false_or] using falseBound _ le
    · have hv : (u = 1 ∧ v = 3) ∨ (u = 3 ∧ v = 1) := of_decide_eq_true hc
      rcases hv with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · simp only [Bool.false_or, Bool.and_true]
      · simpa only [Bool.false_or, Bool.and_true] using congrArg K (support_swap (3 : Fin 9) 1)
  · exact positive _ he

def edgeList (b : Bool) : List (Fin 9 × Fin 9) :=
  (if b then [(1,3)] else []) ++
    [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]

def graph (b : Bool) : SimpleGraph (Fin 9) :=
  SimpleGraph.fromRel (fun i j => (i,j) ∈ edgeList b)

instance (b : Bool) : DecidableRel (graph b).Adj := by
  intro u v
  change Decidable (u ≠ v ∧ ((u,v) ∈ edgeList b ∨ (v,u) ∈ edgeList b))
  infer_instance

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem graph_iff :
    ∀ (b : Bool) (u v : Fin 9),
      (target (support u v) || (b && chord u v)) = true ↔ (graph b).Adj u v := by
  decide +kernel

theorem agrees_graph (K : (Fin 9 → Bool) → Bool) (t : Fin 9)
    (ht : t = 0 ∨ t = 2 ∨ t = 7) (mono : Monotone K)
    (positive : ∀ x, target x = true → K x = true)
    (wired : ∀ x, (x 4 || x 6 || x t) = true → K x = target x) :
    ∃ b : Bool, ∀ u v : Fin 9, K (support u v) = true ↔ (graph b).Adj u v := by
  obtain ⟨b,hb⟩ := agrees K t ht mono positive wired
  refine ⟨b, fun u v => ?_⟩
  rw [hb]
  exact graph_iff b u v

end PEqualNP.Outside.L_meta_4445.PairSemantics

namespace PEqualNP.Outside.L_meta_4445

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem pairLower_of_semantics (C : Circuit) (t : Fin 9)
    (ht : t = 0 ∨ t = 2 ∨ t = 7) (hm : Monotone2 C)
    (mono : Monotone (fun x : Fin 9 → Bool => C.eval (List.ofFn x)))
    (positive : ∀ x, PairSemantics.target x = true → C.eval (List.ofFn x) = true)
    (wired : ∀ x, (x 4 || x 6 || x t) = true →
      C.eval (List.ofFn x) = PairSemantics.target x) :
    13 ≤ C.size := by
  obtain ⟨b,hb⟩ := PairSemantics.agrees_graph _ t ht mono positive wired
  apply PairBound.lower b C hm
  intro u v
  change C.eval (List.ofFn (fun i => decide (i ∈ ({u,v} : Finset (Fin 9))))) = true ↔
    (PairSemantics.graph b).Adj u v
  rw [← PairSemantics.support_finset]
  exact hb u v

theorem pairLower_of_monotone (C : Circuit) (t : Fin 9)
    (ht : t = 0 ∨ t = 2 ∨ t = 7) (hm : Monotone2 C)
    (positive : ∀ x, PairSemantics.target x = true → C.eval (List.ofFn x) = true)
    (wired : ∀ x, (x 4 || x 6 || x t) = true →
      C.eval (List.ofFn x) = PairSemantics.target x) :
    13 ≤ C.size := by
  have compat : ∀ a b : Bool, (a = true → b = true) ↔ a ≤ b := by decide
  have mono : Monotone (fun x : Fin 9 → Bool => C.eval (List.ofFn x)) := by
    intro x y le
    exact (compat _ _).1 (PairBound.acts_mono hm (fun i => (compat _ _).2 (le i)) C.output)
  exact pairLower_of_semantics C t ht hm mono positive wired

end PEqualNP.Outside.L_meta_4445

namespace PEqualNP.Outside.L_meta_4445.CircuitMonotonicity

open PEqualNP.CircuitLowerBounds

private def extend (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem valueMonotone (g : Gate) (hop : g.op = .and ∨ g.op = .or)
    (a b : List Bool) (hle : ∀ i, a.getD i false = true → b.getD i false = true) :
    g.op.eval (g.inputs.map fun i => a.getD i false) = true →
      g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro hall value hvalue
    obtain ⟨i, hi, rfl⟩ := hvalue
    exact hle i (hall _ ⟨i, hi, rfl⟩)
  · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨_, ⟨i, hi, rfl⟩, hvalue⟩
    exact ⟨_, ⟨i, hi, rfl⟩, hle i hvalue⟩

private theorem lastValue (a : List Bool) (b : Bool) :
    (a ++ [b]).getD a.length false = b := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

private theorem foldMonotone (gates : List Gate)
    (hop : ∀ g ∈ gates, g.op = .and ∨ g.op = .or) (a b : List Bool)
    (hlen : a.length = b.length)
    (hle : ∀ i, a.getD i false = true → b.getD i false = true)
    (j : ℕ) (hj : (gates.foldl extend a).getD j false = true) :
    (gates.foldl extend b).getD j false = true := by
  induction gates generalizing a b with
  | nil => exact hle j hj
  | cons g tail ih =>
    apply ih (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
      (extend a g) (extend b g) (by simp [extend, hlen]) ?_ hj
    intro i hi
    unfold extend at hi ⊢
    by_cases low : i < a.length
    · rw [List.getD_append _ _ _ _ low] at hi
      rw [List.getD_append _ _ _ _ (hlen ▸ low)]
      exact hle i hi
    · by_cases eq : i = a.length
      · subst i
        rw [lastValue] at hi
        rw [hlen, lastValue]
        exact valueMonotone g (hop _ List.mem_cons_self) a b hle hi
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
        exact Bool.noConfusion hi

theorem andOrMonotone (C : Circuit) (hop : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or)
    (a b : List Bool) (hlen : a.length = b.length)
    (hle : ∀ i, a.getD i false = true → b.getD i false = true) :
    C.eval a = true → C.eval b = true :=
  foldMonotone C.gates hop a b hlen hle C.output

end PEqualNP.Outside.L_meta_4445.CircuitMonotonicity


namespace PEqualNP.Outside.L_meta_4445.PinTrue

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The constant propagation is adapted from the checked L-meta-1908 proof.
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2


theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp
def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

abbrev Stat : Type := Bool ⊕ ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_start r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2


theorem two_count {α : Type} (p : α → Bool) : ∀ (l : List α) (i j : Fin l.length), i ≠ j →
    p (l.get i) = true → p (l.get j) = true → 2 ≤ l.countP p := by
  intro l
  induction l with
  | nil => intro i; exact i.elim0
  | cons a l ih =>
    intro i j hne hi hj
    have pos : ∀ k : Fin l.length, p (l.get k) = true → 1 ≤ l.countP p := fun k hk =>
      List.countP_pos_iff.2 ⟨l.get k, List.get_mem l k, hk⟩
    rw [List.countP_cons]
    refine Fin.cases (motive := fun i => i ≠ j → p ((a :: l).get i) = true → _) ?_ ?_ i hne hi
    · intro hne hi
      refine Fin.cases (motive := fun j => (0 : Fin (l.length + 1)) ≠ j → p ((a :: l).get j) = true → _) ?_ ?_ j hne hj
      · intro h; exact absurd rfl h
      · intro k _ hk
        have := pos k hk
        have ha : p a = true := hi
        simp only [ha, ite_true]; omega
    · intro m hne hm
      refine Fin.cases (motive := fun j => m.succ ≠ j → p ((a :: l).get j) = true → _) ?_ ?_ j hne hj
      · intro _ ha
        have := pos m hm
        have ha : p a = true := ha
        simp only [ha, ite_true]; omega
      · intro k hne hk
        have := ih m k (fun e => hne (congrArg Fin.succ e)) hm hk
        omega

theorem elim_count (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (elim n gs acc).2.length + gs.countP (fun g => decide (k ∈ g.inputs))
      ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _; simp [elim]
  | cons g gs ih =>
    intro acc hok hk hc
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (by simp [elimStep]; omega)
      (by
        obtain ⟨c, hc⟩ := hc
        refine ⟨c, ?_⟩
        simp only [elimStep]
        rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
    rw [h3, List.length_cons, List.countP_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      simp only [hkg, decide_true, ite_true]
      omega
    · have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      simp only [hkg, decide_false, Bool.false_eq_true, ite_false]
      omega

lemma simplify_same_op (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, g.op = op := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; rfl)
  · simp at hg
  · simp at hg

private theorem preservesMonotone (n : Nat) (gs : List Gate) (acc : List Stat × List Gate)
    (h : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (ha : ∀ g ∈ acc.2, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ (elim n gs acc).2,
      g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction gs generalizing acc with
  | nil => exact ha
  | cons g tail ih =>
    change ∀ g' ∈ (elim n tail (elimStep n acc g)).2, _
    apply ih (elimStep n acc g) (fun g' h' => h g' (List.mem_cons_of_mem g h'))
    intro g' mem
    let x := simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
    change g' ∈ acc.2 ++ x.1.toList at mem
    rcases List.mem_append.mp mem with old | added
    · exact ha g' old
    · have add' : g' ∈ x.1 := by simpa using added
      have same := simplify_same_op g.op _ _ g' add'
      have model := h g List.mem_cons_self
      exact ⟨by simpa [same] using model.1, (simplify_ok g.op _ _ g' add').2⟩

private def initial (n : Nat) : List Stat × List Gate :=
  (List.ofFn (fun i : Fin n => Sum.inr i.val) ++ [Sum.inl true], [])

private theorem ofFnGet {n : Nat} {A : Type} (f : Fin n → A) (a : A) (i : Fin n) :
    (List.ofFn f).getD i.val a = f i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

private theorem initialInv {n : Nat} (x : Fin n → Bool) :
    Inv n (List.ofFn x) (List.ofFn x ++ [true]) (initial n) := by
  refine ⟨by simp [initial], ?_⟩
  intro i
  by_cases h : i < n
  · simp only [initial]
    rw [List.getD_append _ _ _ _ (by simpa using h),
      List.getD_append _ _ _ _ (by simpa using h),
      ofFnGet (fun j : Fin n => Sum.inr j.val) _ ⟨i, h⟩]
    simp [Stat.Valid, Stat.val, wiresFrom, h, List.getD_eq_getElem?_getD]
  · by_cases eq : i = n
    · subst i
      simp only [initial]
      rw [getD_snoc_len _ _ _ _ (by simp), getD_snoc_len _ _ _ _ (by simp)]
      simp [Stat.val, Stat.Valid]
    · have after : n + 1 ≤ i := by omega
      simp only [initial]
      rw [List.getD_eq_default _ _ (by simpa using after), List.getD_eq_default _ _ (by simpa using after)]
      simp [Stat.val, Stat.Valid]

theorem apply {n : Nat} (C : Circuit) (hm : Monotone2 C)
    (nonconstant : ∃ x y : Fin n → Bool,
      C.eval (List.ofFn x ++ [true]) ≠ C.eval (List.ofFn y ++ [true])) :
    ∃ K : Circuit, Monotone2 K ∧
      K.size + C.gates.countP (fun g => decide (n ∈ g.inputs)) ≤ C.size ∧
      ∀ x : Fin n → Bool, K.eval (List.ofFn x) = C.eval (List.ofFn x ++ [true]) := by
  let result := elim n C.gates (initial n)
  have allowed : ∀ g ∈ C.gates, NOk g := by
    intro g hg
    obtain ⟨op, size⟩ := hm g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at op
    rcases op with op | op <;> simp [NOk, Ok, op, size]
  have count := elim_count n n C.gates (initial n) allowed
    (by simp [initial]) ⟨true, by
      unfold initial
      rw [getD_snoc_len _ _ _ _ (by simp)]⟩
  have folded := fun x : Fin n → Bool =>
    inv_elim n (List.ofFn x) (by simp) C.gates (List.ofFn x ++ [true]) (initial n)
      (fun g hg => (allowed g hg).1) (initialInv x)
  have identity (x : Fin n → Bool) :
      (result.1.getD C.output (Sum.inl false)).val (wiresFrom result.2 (List.ofFn x)) =
        C.eval (List.ofFn x ++ [true]) :=
    ((folded x).2 C.output).2
  rcases hcode : result.1.getD C.output (Sum.inl false) with b | wire
  · rcases nonconstant with ⟨x, y, neq⟩
    have hx := identity x
    have hy := identity y
    rw [hcode] at hx hy
    exact False.elim (neq (hx.symm.trans hy))
  · refine ⟨⟨result.2, wire⟩, preservesMonotone n C.gates (initial n) hm (by simp [initial]),
      ?_, ?_⟩
    · simpa [initial, result, Circuit.size] using count
    · intro x
      simpa only [hcode, Stat.val, Circuit.eval, wires_eq] using identity x

theorem intoTrue {n : Nat} (C : Circuit) (hm : Monotone2 C) (x : Fin n → Bool) (bit : Bool) :
    C.eval (List.ofFn x ++ [bit]) = true → C.eval (List.ofFn x ++ [true]) = true := by
  apply CircuitMonotonicity.andOrMonotone C (fun g hg => by simpa using (hm g hg).1)
    (List.ofFn x ++ [bit]) (List.ofFn x ++ [true]) (by simp)
  intro i hi
  by_cases h : i = n
  · subst i
    rw [getD_snoc_len _ _ _ _ (by simp)]
  · rwa [getD_snoc_ne _ _ _ _ (by simpa), ← getD_snoc_ne _ bit _ _ (by simpa)]

theorem countPositive {n : Nat} (C : Circuit) (used : ∃ g ∈ C.gates, n ∈ g.inputs) :
    1 ≤ C.gates.countP (fun g => decide (n ∈ g.inputs)) := by
  obtain ⟨g, hg, hi⟩ := used
  obtain ⟨a, b, h⟩ := List.append_of_mem hg
  rw [h, List.countP_append]
  simp only [List.countP_cons, hi, decide_true, ite_true]
  omega

end PEqualNP.Outside.L_meta_4445.PinTrue

namespace PEqualNP.Outside.L_meta_4445.PinTrue

open PEqualNP.CircuitLowerBounds

private theorem foldAgreeExcept (gs : List Gate) (excluded : Nat)
    (unread : ∀ g ∈ gs, excluded ∉ g.inputs) (a b : List Bool) (hlen : a.length = b.length)
    (agree : ∀ j, j ≠ excluded → a.getD j false = b.getD j false)
    (j : Nat) (hj : j ≠ excluded) :
    (wiresFrom gs a).getD j false = (wiresFrom gs b).getD j false := by
  induction gs generalizing a b with
  | nil => exact agree j hj
  | cons g gs ih =>
    let av := g.op.eval (g.inputs.map fun i => a.getD i false)
    let bv := g.op.eval (g.inputs.map fun i => b.getD i false)
    have valueEq : av = bv := by
      apply congrArg g.op.eval
      exact List.map_congr_left fun i hi =>
        agree i (fun eq => unread g List.mem_cons_self (eq ▸ hi))
    change (wiresFrom gs (a ++ [av])).getD j false =
      (wiresFrom gs (b ++ [bv])).getD j false
    apply ih (fun q hq => unread q (List.mem_cons_of_mem _ hq))
      (a ++ [av]) (b ++ [bv]) (by simp [hlen])
    intro i hi
    by_cases isNew : i = a.length
    · have rhsNew : i = b.length := isNew.trans hlen
      rw [isNew, getD_snoc_eq, ← isNew, rhsNew, getD_snoc_eq]
      exact valueEq
    · have rhsOld : i ≠ b.length := fun eq => isNew (eq.trans hlen.symm)
      rw [getD_snoc_ne _ _ _ _ isNew, getD_snoc_ne _ _ _ _ rhsOld]
      exact agree i hi

theorem hintUnused (D : Circuit) (t : Fin 9)
    (unused : ¬ ∃ g ∈ D.gates, 9 ∈ g.inputs)
    (correct : ∀ x : Fin 9 → Bool,
      D.eval (List.ofFn x ++ [x 4 || x 6 || x t]) = PairSemantics.target x) :
    ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [true]) = PairSemantics.target x := by
  have outputNe : D.output ≠ 9 := by
    intro outputEq
    let probe : Fin 9 → Bool := fun i => decide (i = 4)
    have active : (probe 4 || probe 6 || probe t) = true := by simp [probe]
    have zero : PairSemantics.target probe = false := by decide +kernel
    have bad := correct probe
    rw [active, zero] at bad
    change (wiresFrom D.gates (List.ofFn probe ++ [true])).getD D.output false = false at bad
    rw [outputEq, getD_wiresFrom _ _ _ (by simp)] at bad
    have width : (List.ofFn probe).length = 9 := by simp
    have trueAt : (List.ofFn probe ++ [true]).getD 9 false = true := by
      simpa only [width] using getD_snoc_eq (List.ofFn probe) true false
    exact Bool.noConfusion (trueAt.symm.trans bad)
  intro x
  let base := List.ofFn x
  have width : base.length = 9 := by simp [base]
  have agree : ∀ j, j ≠ 9 →
      (base ++ [true]).getD j false = (base ++ [x 4 || x 6 || x t]).getD j false := by
    intro j hj
    have old : j ≠ base.length := width ▸ hj
    rw [getD_snoc_ne _ _ _ _ old, getD_snoc_ne _ _ _ _ old]
  have eq :=
    foldAgreeExcept D.gates 9 (fun g hg hr => unused ⟨g,hg,hr⟩)
      (base ++ [true]) (base ++ [x 4 || x 6 || x t]) (by simp) agree D.output outputNe
  exact eq.trans (correct x)

end PEqualNP.Outside.L_meta_4445.PinTrue

namespace PEqualNP.Outside.L_meta_4445

namespace SparseBranchBound

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_append_left_lt (w t : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_self (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (step w g) hlt]
    exact getD_append_left_lt w _ i hi

lemma foldl_step_getD_ge (gs : List Gate) (w : List Bool) (i : ℕ) (hi : w.length + gs.length ≤ i) :
    (gs.foldl step w).getD i false = false := by
  apply getD_ge_len
  rw [foldl_step_len]
  exact hi

lemma foldl_step_gate (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate) (hj : gs[j]? = some g) :
    (gs.foldl step w).getD (w.length + j) false =
      g.op.eval (g.inputs.map fun i => if i < w.length + j then (gs.foldl step w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g0 gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [Nat.add_zero, List.foldl_cons]
      have hlt : w.length < (step w g0).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [foldl_step_getD_lt gs (step w g0) w.length hlt]
      have hself : (step w g0).getD w.length false = g0.op.eval (g0.inputs.map fun i => w.getD i false) :=
        getD_append_self w _
      rw [hself]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · have hilt : i < (step w g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]
          omega
        simp only [hi, ↓reduceIte, foldl_step_getD_lt gs (step w g0) i hilt]
        exact (getD_append_left_lt w _ i hi).symm
      · simp only [hi, ↓reduceIte]
        exact getD_ge_len w i (Nat.le_of_not_lt hi)
    | succ j' =>
      simp only [List.getElem?_cons_succ] at hj
      have hlen : (step w g0).length + j' = w.length + (j' + 1) := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [List.foldl_cons, ← hlen]
      exact ih (step w g0) j' hj

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

lemma wires_gate_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      g.op.eval (g.inputs.map fun i => if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
  have h := foldl_step_gate C.gates (List.ofFn x) j g hj
  simpa only [List.length_ofFn, ← wires_eq_foldl] using h

lemma ofFn_getD_lt {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]

lemma wires_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (C.wires (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
  rw [wires_eq_foldl, foldl_step_getD_lt C.gates (List.ofFn x) w (by simp [hw]), ofFn_getD_lt]

lemma wires_oob {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    (C.wires (List.ofFn x)).getD w false = false := by
  rw [wires_eq_foldl]
  exact foldl_step_getD_ge C.gates (List.ofFn x) w (by simp [hw])

lemma gateOp_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (f1 f2 : ℕ → Bool) (hle : ∀ i ∈ l, f1 i = true → f2 i = true) :
    op.eval (l.map f1) = true → op.eval (l.map f2) = true := by
  rcases hop with rfl | rfl
  · intro h
    change (l.map f1).all id = true at h
    change (l.map f2).all id = true
    rw [List.all_eq_true] at h ⊢
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact hle i hi (h _ (List.mem_map_of_mem hi))
  · intro h
    change (l.map f1).any id = true at h
    change (l.map f2).any id = true
    rw [List.any_eq_true] at h ⊢
    obtain ⟨b, hb, hbt⟩ := h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact ⟨f2 i, List.mem_map_of_mem hi, hle i hi hbt⟩

lemma wires_mono {n : ℕ} (C : Circuit) (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ u, x u = true → y u = true) :
    ∀ w : ℕ, (C.wires (List.ofFn x)).getD w false = true → (C.wires (List.ofFn y)).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw1 : w < n
    · rw [wires_input C x w hw1, wires_input C y w hw1]
      exact hxy ⟨w, hw1⟩
    · by_cases hw2 : n + C.gates.length ≤ w
      · rw [wires_oob C x w hw2]
        intro h; exact absurd h (by decide)
      · have hjlt : w - n < C.gates.length := by omega
        set j := w - n
        have hwj : w = n + j := by omega
        have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
        have hgop : (C.gates[j]'hjlt).op = GateOp.and ∨ (C.gates[j]'hjlt).op = GateOp.or := by
          simpa using (hmono _ (List.mem_of_getElem? hg)).1
        rw [hwj, wires_gate_ofFn C x j _ hg, wires_gate_ofFn C y j _ hg]
        apply gateOp_mono _ hgop
        intro i _ hi
        by_cases hilt : i < n + j
        · simp only [hilt, ↓reduceIte] at hi ⊢
          exact ih i (by omega) hi
        · simp only [hilt, ↓reduceIte] at hi
          exact absurd hi (by decide)

abbrev Stat := Sum Bool ℕ

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl b => b
  | Sum.inr k => w.getD k false

def statValid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr k => k < m

lemma statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hk => lt_of_lt_of_le hk h

lemma statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s → statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr k, hk => getD_append_left_lt w t k hk

def simpMono (op : GateOp) (m : ℕ) (ins : List Stat) : Stat × Option Gate :=
  match op with
  | GateOp.and =>
    match ins with
    | [] => (Sum.inl true, none)
    | [s] => (s, none)
    | [s1, s2] =>
      match s1, s2 with
      | Sum.inl false, _ => (Sum.inl false, none)
      | _, Sum.inl false => (Sum.inl false, none)
      | Sum.inl true, s => (s, none)
      | s, Sum.inl true => (s, none)
      | Sum.inr a, Sum.inr b => (Sum.inr m, some ⟨GateOp.and, [a, b]⟩)
    | _ => (Sum.inl false, none)
  | GateOp.or =>
    match ins with
    | [] => (Sum.inl false, none)
    | [s] => (s, none)
    | [s1, s2] =>
      match s1, s2 with
      | Sum.inl true, _ => (Sum.inl true, none)
      | _, Sum.inl true => (Sum.inl true, none)
      | Sum.inl false, s => (s, none)
      | s, Sum.inl false => (s, none)
      | Sum.inr a, Sum.inr b => (Sum.inr m, some ⟨GateOp.or, [a, b]⟩)
    | _ => (Sum.inl false, none)
  | _ => (Sum.inl false, none)

lemma simpMono_ok (op : GateOp) (m : ℕ) (ins : List Stat)
    (hins : ∀ s ∈ ins, statValid m s) :
    let res := simpMono op m ins
    statValid (m + res.2.toList.length) res.1 ∧
    ∀ g, res.2 = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  cases op with
  | and =>
    rcases ins with _ | ⟨s1, _ | ⟨s2, _ | _⟩⟩
    · simp [simpMono, statValid]
    · refine ⟨by simpa [simpMono] using hins s1 (by simp), fun _ h => by simp [simpMono] at h⟩
    · cases s1 with
      | inl b1 =>
        cases b1
        · cases s2 with
          | inl b2 => cases b2 <;> simp [simpMono, statValid]
          | inr _ => simp [simpMono, statValid]
        · cases s2 with
          | inl b2 => cases b2 <;> simp [simpMono, statValid]
          | inr b => refine ⟨by simpa [simpMono] using hins (Sum.inr b) (by simp), fun _ h => by simp [simpMono] at h⟩
      | inr a =>
        cases s2 with
        | inl b2 =>
          cases b2
          · simp [simpMono, statValid]
          · refine ⟨by simpa [simpMono] using hins (Sum.inr a) (by simp), fun _ h => by simp [simpMono] at h⟩
        | inr b =>
          simp [simpMono, statValid]
    · simp [simpMono, statValid]
  | or =>
    rcases ins with _ | ⟨s1, _ | ⟨s2, _ | _⟩⟩
    · simp [simpMono, statValid]
    · refine ⟨by simpa [simpMono] using hins s1 (by simp), fun _ h => by simp [simpMono] at h⟩
    · cases s1 with
      | inl b1 =>
        cases b1
        · cases s2 with
          | inl b2 => cases b2 <;> simp [simpMono, statValid]
          | inr b => refine ⟨by simpa [simpMono] using hins (Sum.inr b) (by simp), fun _ h => by simp [simpMono] at h⟩
        · cases s2 with
          | inl b2 => cases b2 <;> simp [simpMono, statValid]
          | inr _ => simp [simpMono, statValid]
      | inr a =>
        cases s2 with
        | inl b2 =>
          cases b2
          · refine ⟨by simpa [simpMono] using hins (Sum.inr a) (by simp), fun _ h => by simp [simpMono] at h⟩
          · simp [simpMono, statValid]
        | inr b =>
          simp [simpMono, statValid]
    · simp [simpMono, statValid]
  | not => simp [simpMono, statValid]
  | mod _ => simp [simpMono, statValid]
  | maj => simp [simpMono, statValid]

lemma simpMono_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2) :
    let res := simpMono op w.length ins
    statVal (res.2.toList.foldl step w) res.1 = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨s1, _ | ⟨s2, _ | _⟩⟩
    · simp [simpMono, statVal, GateOp.eval]
    · simp [simpMono, statVal, GateOp.eval]
    · cases s1 with
      | inl b1 =>
        cases b1 <;> cases s2 with | inl b2 => cases b2 <;> simp [simpMono, statVal, GateOp.eval] | inr _ => simp [simpMono, statVal, GateOp.eval]
      | inr a =>
        cases s2 with
        | inl b2 =>
          cases b2 <;> simp [simpMono, statVal, GateOp.eval]
        | inr b =>
          simp only [simpMono, Option.toList_some, List.foldl_cons, List.foldl_nil, step, statVal, getD_append_self, GateOp.eval, List.map_cons, List.map_nil]
    · simp at hlen
  · rcases ins with _ | ⟨s1, _ | ⟨s2, _ | _⟩⟩
    · simp [simpMono, statVal, GateOp.eval]
    · simp [simpMono, statVal, GateOp.eval]
    · cases s1 with
      | inl b1 =>
        cases b1 <;> cases s2 with | inl b2 => cases b2 <;> simp [simpMono, statVal, GateOp.eval] | inr _ => simp [simpMono, statVal, GateOp.eval]
      | inr a =>
        cases s2 with
        | inl b2 =>
          cases b2 <;> simp [simpMono, statVal, GateOp.eval]
        | inr b =>
          simp only [simpMono, Option.toList_some, List.foldl_cons, List.foldl_nil, step, statVal, getD_append_self, GateOp.eval, List.map_cons, List.map_nil]
    · simp at hlen

def elimPass (n j0 : ℕ) (repl : List Stat → Stat) (gs : List Gate) : List Stat × List Gate :=
  (gs.zipIdx).foldl (fun acc p =>
    let tbl := acc.1
    let outG := acc.2
    if p.2 = j0 then
      (tbl ++ [repl tbl], outG)
    else
      let ins := p.1.inputs.map (fun i => if i < n + p.2 then tbl.getD i (Sum.inl false) else Sum.inl false)
      let res := simpMono p.1.op (n + outG.length) ins
      (tbl ++ [res.1], outG ++ res.2.toList))
    (List.ofFn (fun i : Fin n => (Sum.inr i.val : Stat)), [])

lemma elim_step_core (n j0 : ℕ) (repl : List Stat → Stat)
    (C : Circuit) (hmono : PEqualNP.MetaComplexity.Monotone2 C) (hj0 : j0 < C.gates.length)
    (skip : Bool)
    (hrepl_valid : ∀ tbl : List Stat, tbl.length = n + j0 →
      (∀ i < n + j0, statValid (n + (elimPass n j0 repl (C.gates.take j0)).2.length) (tbl.getD i (Sum.inl false))) →
      statValid (n + (elimPass n j0 repl (C.gates.take j0)).2.length) (repl tbl))
    (hrepl_val : skip = false → ∀ (x : Fin n → Bool) (tbl : List Stat) (w' : List Bool),
      tbl.length = n + j0 →
      (∀ i < n + j0, statVal w' (tbl.getD i (Sum.inl false)) = (C.wires (List.ofFn x)).getD i false) →
      statVal w' (repl tbl) = (C.wires (List.ofFn x)).getD (n + j0) false)
    (hunused : skip = true → ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → j ≠ j0 → n + j0 ∉ g.inputs) :
    let res := elimPass n j0 repl C.gates
    res.1.length = n + C.gates.length ∧
    res.2.length < C.gates.length ∧
    (∀ g ∈ res.2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
    (∀ i < n + C.gates.length, statValid (n + res.2.length) (res.1.getD i (Sum.inl false))) ∧
    (∀ (x : Fin n → Bool) (i : ℕ), i < n + C.gates.length → (skip = true → i ≠ n + j0) →
      statVal (res.2.foldl step (List.ofFn x)) (res.1.getD i (Sum.inl false)) = (C.wires (List.ofFn x)).getD i false) := by
  have hpref : ∀ k ≤ C.gates.length,
      let res := elimPass n j0 repl (C.gates.take k)
      res.1.length = n + k ∧
      res.2.length ≤ (if j0 < k then k - 1 else k) ∧
      (∀ g ∈ res.2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      (∀ i < n + k, statValid (n + res.2.length) (res.1.getD i (Sum.inl false))) ∧
      (∀ (x : Fin n → Bool) (i : ℕ), i < n + k → (skip = true → i ≠ n + j0) →
        statVal (res.2.foldl step (List.ofFn x)) (res.1.getD i (Sum.inl false)) = (C.wires (List.ofFn x)).getD i false) := by
    intro k hk
    induction k with
    | zero =>
      simp only [List.take_zero, elimPass, List.zipIdx_nil, List.foldl_nil, List.length_ofFn, add_zero, List.length_nil, Nat.not_lt_zero, ↓reduceIte, le_refl, List.not_mem_nil, IsEmpty.forall_iff, imp_true_iff, true_and]
      refine ⟨?_, ?_⟩
      · intro i hi
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, ↓reduceDIte, Option.getD_some, statValid, hi]
      · intro x i hi _
        have hget : (List.ofFn (fun i : Fin n => (Sum.inr i.val : Stat))).getD i (Sum.inl false) = Sum.inr i := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some]
        rw [hget]
        simp only [statVal, wires_input C x i hi, ofFn_getD_lt x i hi]
    | succ k ih =>
      obtain ⟨hlen, hsz, hgm, hval, hsnd⟩ := ih (by omega)
      have hklt : k < C.gates.length := by omega
      have htake : C.gates.take (k + 1) = C.gates.take k ++ [C.gates[k]'hklt] := List.take_succ_eq_append_getElem hklt
      have hzip : (C.gates.take (k + 1)).zipIdx = (C.gates.take k).zipIdx ++ [(C.gates[k]'hklt, k)] := by
        rw [htake, List.zipIdx_append]
        simp [List.length_take, Nat.min_eq_left (by omega : k ≤ C.gates.length)]
      set prev := elimPass n j0 repl (C.gates.take k)
      have hstep : elimPass n j0 repl (C.gates.take (k + 1)) =
          if k = j0 then
            (prev.1 ++ [repl prev.1], prev.2)
          else
            let ins := (C.gates[k]'hklt).inputs.map (fun i => if i < n + k then prev.1.getD i (Sum.inl false) else Sum.inl false)
            let res := simpMono (C.gates[k]'hklt).op (n + prev.2.length) ins
            (prev.1 ++ [res.1], prev.2 ++ res.2.toList) := by
        show ((C.gates.take (k + 1)).zipIdx).foldl _ _ = _
        rw [hzip, List.foldl_append, List.foldl_cons, List.foldl_nil]
        rfl
      rw [hstep]
      by_cases hkj : k = j0
      · subst hkj
        simp only [↓reduceIte, lt_irrefl, Nat.lt_succ_self] at hsz ⊢
        refine ⟨by simp [hlen]; omega, by omega, hgm, ?_, ?_⟩
        · intro i hi
          by_cases hik : i < n + k
          · rw [getD_append_left_lt_stat]
            · exact hval i hik
            · omega
          · have heq : i = n + k := by omega
            subst heq
            have hget : (prev.1 ++ [repl prev.1]).getD (n + k) (Sum.inl false) = repl prev.1 := by
              rw [← hlen]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            rw [hget]
            exact hrepl_valid prev.1 hlen hval
        · intro x i hi hsk
          by_cases hik : i < n + k
          · have hget : (prev.1 ++ [repl prev.1]).getD i (Sum.inl false) = prev.1.getD i (Sum.inl false) := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < prev.1.length)]
            rw [hget]
            exact hsnd x i hik hsk
          · have heq : i = n + k := by omega
            subst heq
            have hskf : skip = false := by
              cases h : skip
              · rfl
              · exact absurd rfl (hsk h)
            have hget : (prev.1 ++ [repl prev.1]).getD (n + k) (Sum.inl false) = repl prev.1 := by
              rw [← hlen]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            rw [hget]
            exact hrepl_val hskf x prev.1 (prev.2.foldl step (List.ofFn x)) hlen (fun i hi => hsnd x i hi (by intro h; rw [hskf] at h; cases h))
      · simp only [hkj, ↓reduceIte]
        set g := C.gates[k]'hklt
        set ins := g.inputs.map (fun i => if i < n + k then prev.1.getD i (Sum.inl false) else Sum.inl false)
        set sm := simpMono g.op (n + prev.2.length) ins
        have hsm_ok := simpMono_ok g.op (n + prev.2.length) ins (fun s hs => by
          obtain ⟨i, _, rfl⟩ := List.mem_map.mp hs
          by_cases hi : i < n + k
          · simp only [hi, ↓reduceIte]; exact hval i hi
          · simp only [hi, ↓reduceIte, statValid])
        have htolen : sm.2.toList.length ≤ 1 := by cases sm.2 <;> simp
        refine ⟨by simp [hlen]; omega, ?_, ?_, ?_, ?_⟩
        · simp only [List.length_append]
          split_ifs at hsz ⊢ <;> omega
        · intro g' hg'
          rcases List.mem_append.mp hg' with hm | hm
          · exact hgm g' hm
          · cases h2 : sm.2 with
            | none => rw [h2] at hm; simp at hm
            | some g0 =>
              rw [h2] at hm
              simp only [Option.toList_some, List.mem_singleton] at hm
              subst hm
              exact hsm_ok.2 g' h2
        · intro i hi
          simp only [List.length_append]
          by_cases hik : i < n + k
          · have hget : (prev.1 ++ [sm.1]).getD i (Sum.inl false) = prev.1.getD i (Sum.inl false) := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < prev.1.length)]
            rw [hget]
            exact statValid_mono (by omega) _ (hval i hik)
          · have heq : i = n + k := by omega
            subst heq
            have hget : (prev.1 ++ [sm.1]).getD (n + k) (Sum.inl false) = sm.1 := by
              rw [← hlen]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            rw [hget]
            rw [← Nat.add_assoc]
            exact hsm_ok.1
        · intro x i hi hsk
          rw [List.foldl_append]
          have hprevlen : (prev.2.foldl step (List.ofFn x)).length = n + prev.2.length := by
            rw [foldl_step_len, List.length_ofFn]
          by_cases hik : i < n + k
          · have hget : (prev.1 ++ [sm.1]).getD i (Sum.inl false) = prev.1.getD i (Sum.inl false) := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < prev.1.length)]
            rw [hget]
            have hkeep : statVal (sm.2.toList.foldl step (prev.2.foldl step (List.ofFn x))) (prev.1.getD i (Sum.inl false)) =
                statVal (prev.2.foldl step (List.ofFn x)) (prev.1.getD i (Sum.inl false)) := by
              have hvi := hval i hik
              cases hs : prev.1.getD i (Sum.inl false) with
              | inl b => rfl
              | inr m =>
                rw [hs] at hvi
                exact foldl_step_getD_lt sm.2.toList _ m (by rw [hprevlen]; exact hvi)
            rw [hkeep]
            exact hsnd x i hik hsk
          · have heq : i = n + k := by omega
            subst heq
            have hget : (prev.1 ++ [sm.1]).getD (n + k) (Sum.inl false) = sm.1 := by
              rw [← hlen]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            rw [hget]
            have hgmem : g ∈ C.gates := List.getElem_mem hklt
            have hgop : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using (hmono g hgmem).1
            have hglen : ins.length ≤ 2 := by simp only [ins, List.length_map]; exact (hmono g hgmem).2
            have hsms := simpMono_sound g.op hgop (prev.2.foldl step (List.ofFn x)) ins hglen
            rw [hprevlen] at hsms
            change statVal (sm.2.toList.foldl step (prev.2.foldl step (List.ofFn x))) sm.1 = _
            rw [hsms]
            have hgetk : C.gates[k]? = some g := List.getElem?_eq_getElem hklt
            rw [wires_gate_ofFn C x k g hgetk]
            congr 1
            simp only [ins, List.map_map]
            apply List.map_congr_left
            intro u hu
            simp only [Function.comp_apply]
            by_cases hu_lt : u < n + k
            · simp only [hu_lt, ↓reduceIte]
              apply hsnd x u hu_lt
              intro hskt hequ
              subst hequ
              exact hunused hskt k g hgetk hkj hu
            · simp only [hu_lt, ↓reduceIte, statVal]
  have hfull := hpref C.gates.length (le_refl _)
  rw [List.take_length] at hfull
  simp only [hj0, ↓reduceIte] at hfull
  exact ⟨hfull.1, by omega, hfull.2.2.1, hfull.2.2.2.1, hfull.2.2.2.2⟩
where
  getD_append_left_lt_stat (w t : List Stat) (i : ℕ) (hi : i < w.length) :
      (w ++ t).getD i (Sum.inl false) = w.getD i (Sum.inl false) := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma elim_smaller_circuit {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Circuit) (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (F : (Fin n → Bool) → Prop)
    (positive : ∀ x, (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → F x)
    (negative : ∀ (x : Fin n → Bool), (∃ a b : Fin n, ∀ i, x i = true → i = a ∨ i = b) →
      F x → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)
    (hfun : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ F x)
    (hedge : ∃ u v : Fin n, G.Adj u v)
    (j0 : ℕ) (hj0 : j0 < C.gates.length)
    (repl : List Stat → Stat) (skip : Bool)
    (hrepl_valid : ∀ tbl : List Stat, tbl.length = n + j0 →
      (∀ i < n + j0, statValid (n + (elimPass n j0 repl (C.gates.take j0)).2.length) (tbl.getD i (Sum.inl false))) →
      statValid (n + (elimPass n j0 repl (C.gates.take j0)).2.length) (repl tbl))
    (hrepl_val : skip = false → ∀ (x : Fin n → Bool) (tbl : List Stat) (w' : List Bool),
      tbl.length = n + j0 →
      (∀ i < n + j0, statVal w' (tbl.getD i (Sum.inl false)) = (C.wires (List.ofFn x)).getD i false) →
      statVal w' (repl tbl) = (C.wires (List.ofFn x)).getD (n + j0) false)
    (hunused : skip = true → (C.output ≠ n + j0 ∧ ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → j ≠ j0 → n + j0 ∉ g.inputs)) :
    ∃ C' : Circuit, PEqualNP.MetaComplexity.Monotone2 C' ∧ C'.size < C.size ∧
      ∀ x : Fin n → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  have hcore := elim_step_core n j0 repl C hmono hj0 skip hrepl_valid hrepl_val (fun h => (hunused h).2)
  set res := elimPass n j0 repl C.gates
  obtain ⟨u0, v0, huv0⟩ := hedge
  have hout_lt : C.output < n + C.gates.length := by
    by_contra hge
    have ht : C.eval (List.ofFn (fun t : Fin n => decide (t = u0 ∨ t = v0))) = true :=
      (hfun _).mpr (positive _ ⟨u0, v0, huv0, by simp, by simp⟩)
    unfold Circuit.eval at ht
    rw [wires_oob C _ C.output (by omega)] at ht
    exact absurd ht (by decide)
  have hzero : C.eval (List.ofFn (fun _ : Fin n => false)) = false := by
    cases h : C.eval (List.ofFn (fun _ : Fin n => false)) with
    | false => rfl
    | true =>
      obtain ⟨_, _, _, hu, _⟩ := negative _ ⟨u0, u0, by simp⟩ ((hfun _).mp h)
      exact absurd hu (by decide)
  have hout_ne : skip = true → C.output ≠ n + j0 := fun h => (hunused h).1
  cases hout : res.1.getD C.output (Sum.inl false) with
  | inl b =>
    cases b
    · have ht := hcore.2.2.2.2 (fun t : Fin n => decide (t = u0 ∨ t = v0)) C.output hout_lt hout_ne
      rw [hout] at ht
      change false = C.eval (List.ofFn (fun t : Fin n => decide (t = u0 ∨ t = v0))) at ht
      have ht2 : C.eval (List.ofFn (fun t : Fin n => decide (t = u0 ∨ t = v0))) = true :=
        (hfun _).mpr (positive _ ⟨u0, v0, huv0, by simp, by simp⟩)
      rw [ht2] at ht; exact absurd ht (by decide)
    · have ht := hcore.2.2.2.2 (fun _ : Fin n => false) C.output hout_lt hout_ne
      rw [hout] at ht
      change true = C.eval (List.ofFn (fun _ : Fin n => false)) at ht
      rw [hzero] at ht; exact absurd ht (by decide)
  | inr wout =>
    refine ⟨⟨res.2, wout⟩, ?_, hcore.2.1, ?_⟩
    · intro g hg
      have := hcore.2.2.1 g hg
      exact ⟨by simpa using this.1, this.2⟩
    · intro x
      have hx := hcore.2.2.2.2 x C.output hout_lt hout_ne
      rw [hout] at hx
      exact hx

def orEndAux (n s : ℕ) (C : Circuit) (outdeg nextOf : ℕ → ℕ)
    (hnext : ∀ w, w < n + s - 1 → outdeg w = 1 → w < n + nextOf w) (w : ℕ) : ℕ :=
  if _h : w < n + s - 1 ∧ outdeg w = 1 then
    if hlt : nextOf w < C.gates.length then
      match (C.gates[nextOf w]'hlt).op with
      | GateOp.or => orEndAux n s C outdeg nextOf hnext (n + nextOf w)
      | _ => w
    else w
  else w
termination_by n + s - w
decreasing_by
  have := hnext w _h.1 _h.2
  omega

def orChainAux (n s : ℕ) (C : Circuit) (outdeg nextOf : ℕ → ℕ)
    (hnext : ∀ w, w < n + s - 1 → outdeg w = 1 → w < n + nextOf w) (w : ℕ) : Finset ℕ :=
  if _h : w < n + s - 1 ∧ outdeg w = 1 then
    if hlt : nextOf w < C.gates.length then
      match (C.gates[nextOf w]'hlt).op with
      | GateOp.or => insert w (orChainAux n s C outdeg nextOf hnext (n + nextOf w))
      | _ => ∅
    else ∅
  else ∅
termination_by n + s - w
decreasing_by
  have := hnext w _h.1 _h.2
  omega

set_option maxHeartbeats 2000000 in
lemma main_bound (n t : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (degree : ∀ v, 2 ≤ G.degree v)
    (hdistinct_nbrs : ∀ v w : Fin n, v ≠ w → ∃ u, G.Adj v u ∧ ¬ G.Adj w u)
    (coverWitness : ∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S →
      S.card = t → ∃ v ∈ S, 3 ≤ G.degree v ∧ 2 ≤ (G.neighborFinset v ∩ (Finset.univ \ S)).card)
    (F : (Fin n → Bool) → Prop)
    (positive : ∀ x, (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → F x)
    (negative : ∀ (x : Fin n → Bool), (∃ a b : Fin n, ∀ i, x i = true → i = a ∨ i = b) →
      F x → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)
    (ht_min : ∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) :
    ∀ s : ℕ, ∀ C : Circuit, C.size = s →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ F x) →
      n + t ≤ s := by
  classical
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro C hCsize hmono hfun
    have hCglen : C.gates.length = s := hCsize
    by_cases hn0 : n = 0
    · subst hn0
      have ht0 : t ≤ 0 := ht_min ∅ (fun u => Fin.elim0 u)
      omega
    have hn1 : 1 ≤ n := by omega
    have hedge : ∃ u v : Fin n, G.Adj u v := by
      let v0 : Fin n := ⟨0, hn1⟩
      have hpos : 0 < (G.neighborFinset v0).card := by have := degree v0; change 2 ≤ (G.neighborFinset v0).card at this; omega
      obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
      exact ⟨v0, u, (SimpleGraph.mem_neighborFinset G v0 u).mp hu⟩
    have hmin : ∀ C' : Circuit, PEqualNP.MetaComplexity.Monotone2 C' → C'.size < s →
        (∀ x : Fin n → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x)) → n + t ≤ s := by
      intro C' hC'm hC'sz hC'eq
      have hC'fun : ∀ x : Fin n → Bool, C'.eval (List.ofFn x) = true ↔ F x := by
        intro x; rw [hC'eq x, hfun x]
      have := ih C'.size hC'sz C' rfl hC'm hC'fun
      omega
    by_contra hlt_goal
    have hnot_smaller : ∀ C' : Circuit, PEqualNP.MetaComplexity.Monotone2 C' → C'.size < s →
        (∀ x : Fin n → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x)) → False :=
      fun C' hm hsz heq => hlt_goal (hmin C' hm hsz heq)
    have hno_const_or_copy : ∀ (j0 : ℕ), j0 < s →
        (¬ ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j0) false = false) ∧
        (¬ ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j0) false = true) ∧
        (∀ w0 < n + j0, ¬ ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j0) false = (C.wires (List.ofFn x)).getD w0 false) := by
      intro j0 hj0
      have hj0len : j0 < C.gates.length := by omega
      refine ⟨?_, ?_, ?_⟩
      · intro hf
        obtain ⟨C', hm', hsz', heq'⟩ := elim_smaller_circuit G C hmono F positive negative hfun hedge j0 hj0len (fun _ => Sum.inl false) false
          (fun _ _ _ => trivial) (fun _ x _ _ _ _ => (hf x).symm) (by intro h; cases h)
        exact hnot_smaller C' hm' (by rw [← hCsize]; exact hsz') heq'
      · intro ht
        obtain ⟨C', hm', hsz', heq'⟩ := elim_smaller_circuit G C hmono F positive negative hfun hedge j0 hj0len (fun _ => Sum.inl true) false
          (fun _ _ _ => trivial) (fun _ x _ _ _ _ => (ht x).symm) (by intro h; cases h)
        exact hnot_smaller C' hm' (by rw [← hCsize]; exact hsz') heq'
      · intro w0 hw0 heqw
        obtain ⟨C', hm', hsz', heq'⟩ := elim_smaller_circuit G C hmono F positive negative hfun hedge j0 hj0len (fun tbl => tbl.getD w0 (Sum.inl false)) false
          (fun tbl _ hv => hv w0 hw0)
          (fun _ x tbl w' _ hvals => (hvals w0 hw0).trans (heqw x).symm)
          (by intro h; cases h)
        exact hnot_smaller C' hm' (by rw [← hCsize]; exact hsz') heq'
    have hgate_shape : ∀ (j : ℕ) (hj : j < C.gates.length),
        ∃ p q : ℕ, (C.gates[j]'hj).inputs = [p, q] ∧ p < n + j ∧ q < n + j ∧ p ≠ q := by
      intro j hj
      have hj_s : j < s := by omega
      have hg : C.gates[j]? = some (C.gates[j]'hj) := List.getElem?_eq_getElem hj
      have hgop : (C.gates[j]'hj).op = GateOp.and ∨ (C.gates[j]'hj).op = GateOp.or := by
        simpa using (hmono _ (List.getElem_mem hj)).1
      have hglen : (C.gates[j]'hj).inputs.length ≤ 2 := (hmono _ (List.getElem_mem hj)).2
      obtain ⟨hnc0, hnc1, hncw⟩ := hno_const_or_copy j hj_s
      rcases hinp : (C.gates[j]'hj).inputs with _ | ⟨p, _ | ⟨q, _ | _⟩⟩
      · rcases hgop with hand | hor
        · exfalso; apply hnc1; intro x; rw [wires_gate_ofFn C x j _ hg, hand, hinp]; rfl
        · exfalso; apply hnc0; intro x; rw [wires_gate_ofFn C x j _ hg, hor, hinp]; rfl
      · by_cases hp : p < n + j
        · exfalso; apply hncw p hp; intro x
          rw [wires_gate_ofFn C x j _ hg, hinp]
          rcases hgop with hand | hor
          · simp [hand, GateOp.eval, hp]
          · simp [hor, GateOp.eval, hp]
        · exfalso; apply hnc0; intro x
          rw [wires_gate_ofFn C x j _ hg, hinp]
          rcases hgop with hand | hor
          · simp [hand, GateOp.eval, hp]
          · simp [hor, GateOp.eval, hp]
      · by_cases hp : p < n + j
        · by_cases hq : q < n + j
          · by_cases hpq : p = q
            · subst hpq
              exfalso; apply hncw p hp; intro x
              rw [wires_gate_ofFn C x j _ hg, hinp]
              rcases hgop with hand | hor
              · simp [hand, GateOp.eval, hp]
              · simp [hor, GateOp.eval, hp]
            · exact ⟨p, q, rfl, hp, hq, hpq⟩
          · rcases hgop with hand | hor
            · exfalso; apply hnc0; intro x; rw [wires_gate_ofFn C x j _ hg, hand, hinp]; simp [GateOp.eval, hq]
            · exfalso; apply hncw p hp; intro x; rw [wires_gate_ofFn C x j _ hg, hor, hinp]; simp [GateOp.eval, hp, hq]
        · rcases hgop with hand | hor
          · exfalso; apply hnc0; intro x; rw [wires_gate_ofFn C x j _ hg, hand, hinp]; simp [GateOp.eval, hp]
          · by_cases hq : q < n + j
            · exfalso; apply hncw q hq; intro x; rw [wires_gate_ofFn C x j _ hg, hor, hinp]; simp [GateOp.eval, hp, hq]
            · exfalso; apply hnc0; intro x; rw [wires_gate_ofFn C x j _ hg, hor, hinp]; simp [GateOp.eval, hp, hq]
      · rw [hinp] at hglen; simp at hglen
    have hout_bounds : n ≤ C.output ∧ C.output < n + s := by
      refine ⟨?_, ?_⟩
      · by_contra hlt
        have hw : C.output < n := by omega
        let v : Fin n := ⟨C.output, hw⟩
        have hfv : C.eval (List.ofFn (fun t : Fin n => decide (t = v))) = false := by
          cases h : C.eval (List.ofFn (fun t : Fin n => decide (t = v))) with
          | false => rfl
          | true =>
            obtain ⟨a, b, hab, ha, hb⟩ := negative _ ⟨v, v, by simp⟩ ((hfun _).mp h)
            simp only [decide_eq_true_eq] at ha hb
            subst ha; subst hb; exact absurd hab (G.loopless.irrefl _)
        unfold Circuit.eval at hfv
        rw [wires_input C _ C.output hw] at hfv
        simp [v] at hfv
      · by_contra hge
        obtain ⟨u0, v0, huv0⟩ := hedge
        have ht : C.eval (List.ofFn (fun t : Fin n => decide (t = u0 ∨ t = v0))) = true :=
          (hfun _).mpr (positive _ ⟨u0, v0, huv0, by simp, by simp⟩)
        unfold Circuit.eval at ht
        rw [wires_oob C _ C.output (by omega)] at ht
        exact absurd ht (by decide)
    have hs_pos : 1 ≤ s := by omega
    have hgate_used : ∀ j < s, n + j ≠ C.output → ∃ j' : Fin C.gates.length, n + j ∈ (C.gates[j'.val]).inputs := by
      intro j hjs hne
      by_contra hnone
      have hjlen : j < C.gates.length := by omega
      obtain ⟨C', hm', hsz', heq'⟩ := elim_smaller_circuit G C hmono F positive negative hfun hedge j hjlen (fun _ => Sum.inl false) true
        (fun _ _ _ => trivial) (by intro h; cases h)
        (fun _ => ⟨hne.symm, fun j' g' hg' _ hmem => by
          have hj'lt : j' < C.gates.length := by
            by_contra hge; rw [List.getElem?_eq_none (by omega)] at hg'; cases hg'
          rw [List.getElem?_eq_getElem hj'lt, Option.some.injEq] at hg'
          subst hg'
          exact hnone ⟨⟨j', hj'lt⟩, hmem⟩⟩)
      exact hnot_smaller C' hm' (by rw [← hCsize]; exact hsz') heq'
    have hout_last : C.output = n + s - 1 := by
      by_contra hne
      have hlast_ne : n + (s - 1) ≠ C.output := by omega
      obtain ⟨j', hj'mem⟩ := hgate_used (s - 1) (by omega) hlast_ne
      obtain ⟨p, q, hpq, hp, hq, _⟩ := hgate_shape j'.val j'.isLt
      rw [hpq] at hj'mem
      have hj's : j'.val < s := by have := j'.isLt; omega
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'mem
      rcases hj'mem with h | h <;> omega
    let outdeg : ℕ → ℕ := fun w => ∑ j : Fin C.gates.length, (C.gates[j.val]).inputs.count w
    have hcount_mem : ∀ (j : Fin C.gates.length) (w : ℕ),
        (C.gates[j.val]).inputs.count w = if w ∈ (C.gates[j.val]).inputs then 1 else 0 := by
      intro j w
      obtain ⟨p, q, hpq, _, _, hne⟩ := hgate_shape j.val j.isLt
      rw [hpq]
      by_cases hwp : w = p
      · subst hwp; simp [hne]
      · by_cases hwq : w = q
        · subst hwq; simp [hwp, Ne.symm hwp]
        · simp [hwp, Ne.symm hwp, hwq, Ne.symm hwq]
    have houtdeg_card : ∀ w : ℕ, outdeg w = (Finset.univ.filter (fun j : Fin C.gates.length => w ∈ (C.gates[j.val]).inputs)).card := by
      intro w
      simp only [outdeg, hcount_mem, Finset.sum_boole, Nat.cast_id]
    have hinput_used : ∀ v : Fin n, 1 ≤ outdeg v.val := by
      intro v
      by_contra h0
      have hzero : outdeg v.val = 0 := by omega
      rw [houtdeg_card, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hzero
      have hno_read : ∀ j : Fin C.gates.length, v.val ∉ (C.gates[j.val]).inputs := fun j hj =>
        hzero j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
      have hpos : 0 < (G.neighborFinset v).card := by have := degree v; change 2 ≤ (G.neighborFinset v).card at this; omega
      obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
      have hvu : G.Adj v u := (SimpleGraph.mem_neighborFinset G v u).mp hu
      have hvu_ne : v ≠ u := G.ne_of_adj hvu
      let x : Fin n → Bool := fun t => decide (t = u)
      let x' : Fin n → Bool := Function.update x v true
      have hind : ∀ w : ℕ, w ≠ v.val → (C.wires (List.ofFn x)).getD w false = (C.wires (List.ofFn x')).getD w false := by
        intro w
        induction w using Nat.strong_induction_on with
        | ind w ihw =>
          intro hwv
          by_cases hw1 : w < n
          · rw [wires_input C x w hw1, wires_input C x' w hw1]
            have hne : (⟨w, hw1⟩ : Fin n) ≠ v := fun h => hwv (congrArg Fin.val h)
            exact (Function.update_of_ne hne true x).symm
          · by_cases hw2 : n + C.gates.length ≤ w
            · rw [wires_oob C x w hw2, wires_oob C x' w hw2]
            · have hjlt : w - n < C.gates.length := by omega
              set j := w - n
              have hwj : w = n + j := by omega
              have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
              rw [hwj, wires_gate_ofFn C x j _ hg, wires_gate_ofFn C x' j _ hg]
              congr 1
              apply List.map_congr_left
              intro k hk
              have hkv : k ≠ v.val := fun h => hno_read ⟨j, hjlt⟩ (h ▸ hk)
              by_cases hklt : k < n + j
              · simp only [hklt, ↓reduceIte]; exact ihw k (by omega) hkv
              · simp only [hklt, ↓reduceIte]
      have heq := hind C.output (by omega)
      change C.eval (List.ofFn x) = C.eval (List.ofFn x') at heq
      have hf1 : C.eval (List.ofFn x) = false := by
        cases h : C.eval (List.ofFn x) with
        | false => rfl
        | true =>
          obtain ⟨a, b, hab, ha, hb⟩ := negative _ ⟨u, u, by simp [x]⟩ ((hfun x).mp h)
          simp only [x, decide_eq_true_eq] at ha hb
          subst ha; subst hb; exact absurd hab (G.loopless.irrefl _)
      have hf2 : C.eval (List.ofFn x') = true := by
        rw [hfun]
        apply positive
        exact ⟨v, u, hvu, by simp [x'], by simp [x', x, hvu_ne.symm]⟩
      rw [hf1, hf2] at heq; exact absurd heq (by decide)
    have houtdeg_ge1 : ∀ w < n + s - 1, 1 ≤ outdeg w := by
      intro w hw
      by_cases hwn : w < n
      · exact hinput_used ⟨w, hwn⟩
      · have hj : w - n < s := by omega
        have hwj : w = n + (w - n) := by omega
        obtain ⟨j', hj'm⟩ := hgate_used (w - n) hj (by omega)
        rw [houtdeg_card]
        exact Finset.card_pos.mpr ⟨j', Finset.mem_filter.mpr ⟨Finset.mem_univ j', hwj ▸ hj'm⟩⟩
    have houtdeg_sum : ∑ w ∈ Finset.range (n + s - 1), outdeg w = 2 * s := by
      have hswap : ∑ w ∈ Finset.range (n + s - 1), outdeg w =
          ∑ j : Fin C.gates.length, ∑ w ∈ Finset.range (n + s - 1), (C.gates[j.val]).inputs.count w :=
        Finset.sum_comm
      rw [hswap]
      have heach : ∀ j : Fin C.gates.length, ∑ w ∈ Finset.range (n + s - 1), (C.gates[j.val]).inputs.count w = 2 := by
        intro j
        obtain ⟨p, q, hpq, hp, hq, hne⟩ := hgate_shape j.val j.isLt
        have hj_s : j.val < s := by have := j.isLt; omega
        have hp_mem : p ∈ Finset.range (n + s - 1) := Finset.mem_range.mpr (by omega)
        have hq_mem : q ∈ Finset.range (n + s - 1) := Finset.mem_range.mpr (by omega)
        have hsub : ({p, q} : Finset ℕ) ⊆ Finset.range (n + s - 1) := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        rw [← Finset.sum_subset hsub]
        · rw [Finset.sum_pair hne, hpq]
          simp [hne, Ne.symm hne]
        · intro w _ hw
          rw [hpq]
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
          simp [Ne.symm hw.1, Ne.symm hw.2]
      simp only [heach, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      have hlen : C.gates.length = s := hCsize
      omega
    have hsurplus_sum : (∑ w ∈ Finset.range (n + s - 1), (outdeg w - 1)) + n = s + 1 := by
      have hadd : ∑ w ∈ Finset.range (n + s - 1), (outdeg w - 1) + ∑ _w ∈ Finset.range (n + s - 1), 1 =
          ∑ w ∈ Finset.range (n + s - 1), outdeg w := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro w hw
        have := houtdeg_ge1 w (Finset.mem_range.mp hw)
        omega
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one, houtdeg_sum] at hadd
      omega
    have hnext_uniq : ∀ w < n + s - 1, outdeg w = 1 →
        ∃! j : Fin C.gates.length, w ∈ (C.gates[j.val]).inputs := by
      intro w _ h1
      rw [houtdeg_card, Finset.card_eq_one] at h1
      obtain ⟨j, hj⟩ := h1
      have hjmem : j ∈ Finset.univ.filter (fun j : Fin C.gates.length => w ∈ (C.gates[j.val]).inputs) :=
        hj ▸ Finset.mem_singleton_self j
      refine ⟨j, (Finset.mem_filter.mp hjmem).2, ?_⟩
      intro j' hj'
      have hj'mem : j' ∈ ({j} : Finset (Fin C.gates.length)) :=
        hj ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ j', hj'⟩
      exact Finset.mem_singleton.mp hj'mem
    let nextOf : (w : ℕ) → ℕ := fun w =>
      if h : w < n + s - 1 ∧ outdeg w = 1 then
        (hnext_uniq w h.1 h.2).choose.val
      else
        0
    have hnextOf_spec : ∀ w, w < n + s - 1 → outdeg w = 1 →
        ∃ hlt : nextOf w < C.gates.length, w ∈ (C.gates[nextOf w]'hlt).inputs ∧
          ∀ j : Fin C.gates.length, w ∈ (C.gates[j.val]).inputs → j.val = nextOf w := by
      intro w hw h1
      have hdef : nextOf w = (hnext_uniq w hw h1).choose.val := by simp [nextOf, hw, h1]
      have hsp := (hnext_uniq w hw h1).choose_spec
      refine ⟨by rw [hdef]; exact (hnext_uniq w hw h1).choose.isLt, ?_, ?_⟩
      · simpa [hdef] using hsp.1
      · intro j hj; rw [hdef]; exact congrArg Fin.val (hsp.2 j hj)
    have hnextOf_gt : ∀ w, w < n + s - 1 → outdeg w = 1 → w < n + nextOf w := by
      intro w hw h1
      obtain ⟨hlt, hmem, _⟩ := hnextOf_spec w hw h1
      obtain ⟨p, q, hpq, hp, hq, _⟩ := hgate_shape (nextOf w) hlt
      rw [hpq] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl <;> assumption
    let orEnd : ℕ → ℕ := orEndAux n s C outdeg nextOf hnextOf_gt
    let orChain : ℕ → Finset ℕ := orChainAux n s C outdeg nextOf hnextOf_gt
    have horEnd_ge : ∀ w, w ≤ orEnd w := by
      intro w
      induction hrem : n + s - w using Nat.strong_induction_on generalizing w with
      | ind rem ihr =>
        dsimp only [orEnd]; rw [orEndAux]
        split_ifs with h hlt
        · cases hop : (C.gates[nextOf w]'hlt).op with
          | or =>
            have hgt := hnextOf_gt w h.1 h.2
            have hrec := ihr (n + s - (n + nextOf w)) (by omega) (n + nextOf w) rfl
            change w ≤ orEnd (n + nextOf w)
            omega
          | and => exact le_refl w
          | not => exact le_refl w
          | mod _ => exact le_refl w
          | maj => exact le_refl w
        · exact le_refl w
        · exact le_refl w
    have horEnd_lt : ∀ w, w < n + s → orEnd w < n + s := by
      intro w hw
      induction hrem : n + s - w using Nat.strong_induction_on generalizing w with
      | ind rem ihr =>
        dsimp only [orEnd]; rw [orEndAux]
        split_ifs with h hlt
        · cases hop : (C.gates[nextOf w]'hlt).op with
          | or =>
            have hgt := hnextOf_gt w h.1 h.2
            have hns : nextOf w < s := by omega
            exact ihr (n + s - (n + nextOf w)) (by omega) (n + nextOf w) (by omega) rfl
          | and => exact hw
          | not => exact hw
          | mod _ => exact hw
          | maj => exact hw
        · exact hw
        · exact hw
    have horEnd_true : ∀ (w : ℕ) (x : Fin n → Bool), w < n + s → (C.wires (List.ofFn x)).getD w false = true →
        (C.wires (List.ofFn x)).getD (orEnd w) false = true := by
      intro w x hw hwt
      induction hrem : n + s - w using Nat.strong_induction_on generalizing w with
      | ind rem ihr =>
        dsimp only [orEnd]; rw [orEndAux]
        split_ifs with h hlt
        · cases hop : (C.gates[nextOf w]'hlt).op with
          | or =>
            have hgt := hnextOf_gt w h.1 h.2
            have hns : nextOf w < s := by omega
            obtain ⟨hlt', hmem, _⟩ := hnextOf_spec w h.1 h.2
            have hg : C.gates[nextOf w]? = some (C.gates[nextOf w]'hlt) := List.getElem?_eq_getElem hlt
            have hnext_t : (C.wires (List.ofFn x)).getD (n + nextOf w) false = true := by
              rw [wires_gate_ofFn C x (nextOf w) _ hg, hop]
              change ((C.gates[nextOf w]'hlt).inputs.map fun i => if i < n + nextOf w then (C.wires (List.ofFn x)).getD i false else false).any id = true
              rw [List.any_eq_true]
              exact ⟨_, List.mem_map_of_mem hmem, by simp only [id_eq, hgt, ↓reduceIte, hwt]⟩
            exact ihr (n + s - (n + nextOf w)) (by omega) (n + nextOf w) (by omega) hnext_t rfl
          | and => exact hwt
          | not => exact hwt
          | mod _ => exact hwt
          | maj => exact hwt
        · exact hwt
        · exact hwt
    have horEnd_stop : ∀ w, w < n + s - 1 →
        (orEnd w = n + s - 1) ∨
        (orEnd w < n + s - 1 ∧ 2 ≤ outdeg (orEnd w)) ∨
        (orEnd w < n + s - 1 ∧ outdeg (orEnd w) = 1 ∧
          ∃ hlt : nextOf (orEnd w) < C.gates.length, (C.gates[nextOf (orEnd w)]'hlt).op = GateOp.and) := by
      intro w hw
      induction hrem : n + s - w using Nat.strong_induction_on generalizing w with
      | ind rem ihr =>
        dsimp only [orEnd]; rw [orEndAux]
        by_cases h1 : w < n + s - 1 ∧ outdeg w = 1
        · obtain ⟨hlt, _, _⟩ := hnextOf_spec w h1.1 h1.2
          simp only [h1, ↓reduceDIte, hlt]
          have hgop : (C.gates[nextOf w]'hlt).op = GateOp.and ∨ (C.gates[nextOf w]'hlt).op = GateOp.or := by
            simpa using (hmono _ (List.getElem_mem hlt)).1
          rcases hgop with hand | hor
          · simp only [hand]
            exact Or.inr (Or.inr ⟨hw, h1.2, hlt, hand⟩)
          · simp only [hor]
            have hgt := hnextOf_gt w h1.1 h1.2
            have hns : nextOf w < s := by omega
            by_cases hlast : n + nextOf w = n + s - 1
            · left
              rw [hlast]
              rw [orEndAux]
              simp
            · exact ihr (n + s - (n + nextOf w)) (by omega) (n + nextOf w) (by omega) rfl
        · simp only [h1, ↓reduceDIte]
          have hge1 := houtdeg_ge1 w hw
          have hne1 : outdeg w ≠ 1 := fun h => h1 ⟨hw, h⟩
          exact Or.inr (Or.inl ⟨hw, by omega⟩)
    have horChain_props : ∀ w, w < n + s →
        (w ∉ orChain w → w = orEnd w) ∧
        (∀ u ∈ orChain w, u < orEnd w ∧ u < n + s - 1 ∧ outdeg u = 1 ∧
          (n + nextOf u ∈ orChain w ∨ n + nextOf u = orEnd w)) := by
      intro w hw
      induction hrem : n + s - w using Nat.strong_induction_on generalizing w with
      | ind rem ihr =>
        dsimp only [orChain, orEnd]; rw [orChainAux, orEndAux]
        split_ifs with h hlt
        · cases hop : (C.gates[nextOf w]'hlt).op with
          | or =>
            have hgt := hnextOf_gt w h.1 h.2
            have hns : nextOf w < s := by omega
            obtain ⟨hrec1, hrec2⟩ := ihr (n + s - (n + nextOf w)) (by omega) (n + nextOf w) (by omega) rfl
            refine ⟨fun hnot => absurd (Finset.mem_insert_self w _) hnot, ?_⟩
            intro u hu
            rcases Finset.mem_insert.mp hu with huw | hu'
            · subst huw
              have hge := horEnd_ge (n + nextOf u)
              refine ⟨by change u < orEnd (n + nextOf u); omega, h.1, h.2, ?_⟩
              by_cases hmem : n + nextOf u ∈ orChain (n + nextOf u)
              · exact Or.inl (Finset.mem_insert_of_mem hmem)
              · exact Or.inr (hrec1 hmem)
            · obtain ⟨h1, h2, h3, h4⟩ := hrec2 u hu'
              exact ⟨h1, h2, h3, h4.imp Finset.mem_insert_of_mem id⟩
          | and => simp
          | not => simp
          | mod _ => simp
          | maj => simp
        · simp
        · simp
    have horChain_in : ∀ w u, u ∈ orChain w → w ≤ u := by
      intro w u hu
      induction hrem : n + s - w using Nat.strong_induction_on generalizing w with
      | ind rem ihr =>
        dsimp only [orChain] at hu; rw [orChainAux] at hu
        split_ifs at hu with h hlt
        · cases hop : (C.gates[nextOf w]'hlt).op with
          | or =>
            rw [hop] at hu
            rcases Finset.mem_insert.mp hu with rfl | hu'
            · exact le_refl u
            · have hgt := hnextOf_gt w h.1 h.2
              have hrec := ihr (n + s - (n + nextOf w)) (by omega) (n + nextOf w) hu' rfl
              omega
          | and => rw [hop] at hu; simp at hu
          | not => rw [hop] at hu; simp at hu
          | mod _ => rw [hop] at hu; simp at hu
          | maj => rw [hop] at hu; simp at hu
        · simp at hu
        · simp at hu
    have horChain_self_or : ∀ w, w < n + s → w ∈ orChain w ∨ w = orEnd w := by
      intro w hw
      by_cases h : w ∈ orChain w
      · exact Or.inl h
      · exact Or.inr ((horChain_props w hw).1 h)
    have horEnd_sole_exit : ∀ (v : Fin n) (x y : Fin n → Bool),
        (∀ t : Fin n, t ≠ v → x t = y t) →
        (C.wires (List.ofFn x)).getD (orEnd v.val) false = (C.wires (List.ofFn y)).getD (orEnd v.val) false →
        ∀ u : ℕ, u < n + s → u ∉ orChain v.val →
          (C.wires (List.ofFn x)).getD u false = (C.wires (List.ofFn y)).getD u false := by
      intro v x y hxy hseq u hu
      induction u using Nat.strong_induction_on with
      | ind u ihu =>
        intro hunot
        by_cases hueq : u = orEnd v.val
        · rw [hueq]; exact hseq
        · by_cases hu1 : u < n
          · rw [wires_input C x u hu1, wires_input C y u hu1]
            have hne : (⟨u, hu1⟩ : Fin n) ≠ v := by
              intro h
              have huv : u = v.val := congrArg Fin.val h
              subst huv
              rcases horChain_self_or v.val (by omega) with hm | he
              · exact hunot hm
              · exact hueq he
            exact hxy ⟨u, hu1⟩ hne
          · have hjlt : u - n < C.gates.length := by have : C.gates.length = s := hCsize; omega
            set j := u - n
            have huj : u = n + j := by omega
            have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
            rw [huj, wires_gate_ofFn C x j _ hg, wires_gate_ofFn C y j _ hg]
            congr 1
            apply List.map_congr_left
            intro k hk
            by_cases hklt : k < n + j
            · simp only [hklt, ↓reduceIte]
              apply ihu k (by omega) (by omega)
              intro hkch
              obtain ⟨_, hklt1, hk1, hknxt⟩ := (horChain_props v.val (by omega)).2 k hkch
              obtain ⟨_, _, huniq⟩ := hnextOf_spec k hklt1 hk1
              have hjeq : j = nextOf k := huniq ⟨j, hjlt⟩ hk
              rw [hjeq] at huj
              rcases hknxt with h1 | h2
              · exact hunot (huj ▸ h1)
              · exact hueq (huj ▸ h2)
            · simp only [hklt, ↓reduceIte]
    have hs_ne_out : ∀ v : Fin n, orEnd v.val < n + s - 1 := by
      intro v
      have hlt := horEnd_lt v.val (by omega)
      by_contra hge
      have heq : orEnd v.val = C.output := by omega
      have h1 : (C.wires (List.ofFn (fun t : Fin n => decide (t = v)))).getD (orEnd v.val) false = true := by
        apply horEnd_true v.val _ (by omega)
        rw [wires_input C _ v.val v.isLt]; simp
      rw [heq] at h1
      change C.eval (List.ofFn (fun t : Fin n => decide (t = v))) = true at h1
      obtain ⟨a, b, hab, ha, hb⟩ := negative _ ⟨v, v, by simp⟩ ((hfun _).mp h1)
      simp only [decide_eq_true_eq] at ha hb
      subst ha; subst hb; exact G.loopless.irrefl _ hab
    have hs_zero_other : ∀ v q : Fin n, q ≠ v →
        (C.wires (List.ofFn (fun t : Fin n => decide (t = q)))).getD (orEnd v.val) false = false := by
      intro v q hqv
      by_contra hne
      have htrue : (C.wires (List.ofFn (fun t : Fin n => decide (t = q)))).getD (orEnd v.val) false = true := by
        cases h : (C.wires (List.ofFn (fun t : Fin n => decide (t = q)))).getD (orEnd v.val) false
        · exact absurd h hne
        · rfl
      have hout_not_ch : C.output ∉ orChain v.val := by
        intro hmem
        have := (horChain_props v.val (by omega)).2 C.output hmem
        omega
      by_cases hadj : G.Adj v q
      · let x : Fin n → Bool := fun t => decide (t = q)
        let y : Fin n → Bool := Function.update x v true
        have hy_true : (C.wires (List.ofFn y)).getD (orEnd v.val) false = true := by
          apply horEnd_true v.val y (by omega)
          rw [wires_input C y v.val v.isLt]
          have : (⟨v.val, v.isLt⟩ : Fin n) = v := Fin.ext rfl
          rw [this]; simp [y]
        have heq := horEnd_sole_exit v x y (fun t ht => (Function.update_of_ne ht true x).symm)
          (htrue.trans hy_true.symm) C.output (by omega) hout_not_ch
        change C.eval (List.ofFn x) = C.eval (List.ofFn y) at heq
        have hf0 : C.eval (List.ofFn x) = false := by
          cases h : C.eval (List.ofFn x) with
          | false => rfl
          | true =>
            obtain ⟨a, b, hab, ha, hb⟩ := negative _ ⟨q, q, by simp [x]⟩ ((hfun x).mp h)
            simp only [x, decide_eq_true_eq] at ha hb
            subst ha; subst hb; exact absurd hab (G.loopless.irrefl _)
        have hf1 : C.eval (List.ofFn y) = true := by
          rw [hfun]
          apply positive
          exact ⟨v, q, hadj, by simp [y], by simp [y, x, hqv]⟩
        rw [hf0, hf1] at heq; exact absurd heq (by decide)
      · obtain ⟨u, hvu, hnw⟩ := hdistinct_nbrs v q hqv.symm
        have huv : u ≠ v := (G.ne_of_adj hvu).symm
        let x : Fin n → Bool := fun t => decide (t = q ∨ t = u)
        let y : Fin n → Bool := Function.update x v true
        have hx_true : (C.wires (List.ofFn x)).getD (orEnd v.val) false = true :=
          wires_mono C hmono (fun t => decide (t = q)) x (fun t ht => by simp only [x, decide_eq_true_eq] at ht ⊢; exact Or.inl ht) (orEnd v.val) htrue
        have hy_true : (C.wires (List.ofFn y)).getD (orEnd v.val) false = true := by
          apply horEnd_true v.val y (by omega)
          rw [wires_input C y v.val v.isLt]
          have : (⟨v.val, v.isLt⟩ : Fin n) = v := Fin.ext rfl
          rw [this]; simp [y]
        have heq := horEnd_sole_exit v x y (fun t ht => (Function.update_of_ne ht true x).symm)
          (hx_true.trans hy_true.symm) C.output (by omega) hout_not_ch
        change C.eval (List.ofFn x) = C.eval (List.ofFn y) at heq
        have hf0 : C.eval (List.ofFn x) = false := by
          cases h : C.eval (List.ofFn x) with
          | false => rfl
          | true =>
            obtain ⟨a, b, hab, ha, hb⟩ := negative _ ⟨q, u, by simp [x]⟩ ((hfun x).mp h)
            simp only [x, decide_eq_true_eq] at ha hb
            rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
            · exact absurd hab (G.loopless.irrefl _)
            · exact absurd hab hnw
            · exact absurd hab.symm hnw
            · exact absurd hab (G.loopless.irrefl _)
        have hf1 : C.eval (List.ofFn y) = true := by
          rw [hfun]
          apply positive
          exact ⟨v, u, hvu, by simp [y], by simp [y, x, huv]⟩
        rw [hf0, hf1] at heq; exact absurd heq (by decide)
    have hs_inj : Function.Injective (fun v : Fin n => orEnd v.val) := by
      intro v w hvw
      by_contra hne
      have h1 : (C.wires (List.ofFn (fun t : Fin n => decide (t = v)))).getD (orEnd v.val) false = true := by
        apply horEnd_true v.val _ (by omega)
        rw [wires_input C _ v.val v.isLt]; simp
      have h2 := hs_zero_other w v hne
      dsimp only at hvw
      rw [hvw, h2] at h1
      exact absurd h1 (by decide)
    set Tbranch : Finset (Fin n) := Finset.univ.filter (fun v : Fin n => 2 ≤ outdeg (orEnd v.val))
    have hand_exit : ∀ v : Fin n, v ∉ Tbranch →
        outdeg (orEnd v.val) = 1 ∧
        ∃ hlt : nextOf (orEnd v.val) < C.gates.length, (C.gates[nextOf (orEnd v.val)]'hlt).op = GateOp.and := by
      intro v hv
      have hnot2 : ¬ 2 ≤ outdeg (orEnd v.val) := fun h => hv (Finset.mem_filter.mpr ⟨Finset.mem_univ v, h⟩)
      have hlt := hs_ne_out v
      rcases horEnd_stop v.val (by omega) with h1 | h2 | h3
      · omega
      · omega
      · exact ⟨h3.2.1, h3.2.2⟩
    have hand_sole_exit : ∀ (v : Fin n) (hv : v ∉ Tbranch) (x y : Fin n → Bool),
        (∀ t : Fin n, t ≠ v → x t = y t) →
        (C.wires (List.ofFn x)).getD (n + nextOf (orEnd v.val)) false =
        (C.wires (List.ofFn y)).getD (n + nextOf (orEnd v.val)) false →
        ∀ u : ℕ, u < n + s → u ∉ orChain v.val → u ≠ orEnd v.val →
          (C.wires (List.ofFn x)).getD u false = (C.wires (List.ofFn y)).getD u false := by
      intro v hv x y hxy haeq u hu
      obtain ⟨h1, hlt_a, _⟩ := hand_exit v hv
      have hlt_s := hs_ne_out v
      induction u using Nat.strong_induction_on with
      | ind u ihu =>
        intro hunot hune
        by_cases hueq : u = n + nextOf (orEnd v.val)
        · rw [hueq]; exact haeq
        · by_cases hu1 : u < n
          · rw [wires_input C x u hu1, wires_input C y u hu1]
            have hne : (⟨u, hu1⟩ : Fin n) ≠ v := by
              intro h
              have huv : u = v.val := congrArg Fin.val h
              subst huv
              rcases horChain_self_or v.val (by omega) with hm | he
              · exact hunot hm
              · exact hune he
            exact hxy ⟨u, hu1⟩ hne
          · have hjlt : u - n < C.gates.length := by have : C.gates.length = s := hCsize; omega
            set j := u - n
            have huj : u = n + j := by omega
            have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
            rw [huj, wires_gate_ofFn C x j _ hg, wires_gate_ofFn C y j _ hg]
            congr 1
            apply List.map_congr_left
            intro k hk
            by_cases hklt : k < n + j
            · simp only [hklt, ↓reduceIte]
              apply ihu k (by omega) (by omega)
              · intro hkch
                obtain ⟨_, hklt1, hk1, hknxt⟩ := (horChain_props v.val (by omega)).2 k hkch
                obtain ⟨_, _, huniq⟩ := hnextOf_spec k hklt1 hk1
                have hjeq : j = nextOf k := huniq ⟨j, hjlt⟩ hk
                rw [hjeq] at huj
                rcases hknxt with h1' | h2'
                · exact hunot (huj ▸ h1')
                · exact hune (huj ▸ h2')
              · intro hks
                subst hks
                obtain ⟨_, _, huniq⟩ := hnextOf_spec (orEnd v.val) hlt_s h1
                have hjeq : j = nextOf (orEnd v.val) := huniq ⟨j, hjlt⟩ hk
                exact hueq (by rw [huj, hjeq])
            · simp only [hklt, ↓reduceIte]
    have hother_input_and : ∀ (v : Fin n) (hv : v ∉ Tbranch),
        let j := nextOf (orEnd v.val)
        ∃ (hlt : j < C.gates.length) (z : ℕ),
          ((C.gates[j]'hlt).inputs = [orEnd v.val, z] ∨ (C.gates[j]'hlt).inputs = [z, orEnd v.val]) ∧
          z < n + j ∧ z ≠ orEnd v.val ∧ z ∉ orChain v.val := by
      intro v hv
      obtain ⟨h1, hlt, hand⟩ := hand_exit v hv
      obtain ⟨_, hmem, _⟩ := hnextOf_spec (orEnd v.val) (hs_ne_out v) h1
      obtain ⟨p, q, hpq, hp, hq, hne⟩ := hgate_shape (nextOf (orEnd v.val)) hlt
      rw [hpq] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      have hnot_ch : ∀ z, z ∈ (C.gates[nextOf (orEnd v.val)]'hlt).inputs → z ∉ orChain v.val := by
        intro z hz hch
        obtain ⟨_, zlt1, z1, _⟩ := (horChain_props v.val (by omega)).2 z hch
        obtain ⟨_, _, huniq⟩ := hnextOf_spec z zlt1 z1
        have hjeq : nextOf (orEnd v.val) = nextOf z := huniq ⟨nextOf (orEnd v.val), hlt⟩ hz

        have : (C.gates[nextOf z]'(hjeq ▸ hlt)).op = GateOp.or := by
          have hzprops : ∀ w0, w0 < n + s → ∀ u ∈ orChain w0,
              ∃ hlt' : nextOf u < C.gates.length, (C.gates[nextOf u]'hlt').op = GateOp.or := by
            intro w0 hw0
            induction hrem : n + s - w0 using Nat.strong_induction_on generalizing w0 with
            | ind rem ihr =>
              intro u hu
              dsimp only [orChain] at hu; rw [orChainAux] at hu
              split_ifs at hu with h' hlt'
              · cases hop' : (C.gates[nextOf w0]'hlt').op with
                | or =>
                  rw [hop'] at hu
                  rcases Finset.mem_insert.mp hu with rfl | hu'
                  · exact ⟨hlt', hop'⟩
                  · have hgt := hnextOf_gt w0 h'.1 h'.2
                    have hns : nextOf w0 < s := by omega
                    exact ihr (n + s - (n + nextOf w0)) (by omega) (n + nextOf w0) (by omega) rfl u hu'
                | and => rw [hop'] at hu; simp at hu
                | not => rw [hop'] at hu; simp at hu
                | mod _ => rw [hop'] at hu; simp at hu
                | maj => rw [hop'] at hu; simp at hu
              · simp at hu
              · simp at hu
          obtain ⟨hlt', hor'⟩ := hzprops v.val (by omega) z hch
          exact hor'
        have hbad : (C.gates[nextOf (orEnd v.val)]'hlt).op = GateOp.or := by
          simpa [hjeq] using this
        rw [hand] at hbad; cases hbad
      rcases hmem with rfl | rfl
      · exact ⟨hlt, q, Or.inl hpq, hq, hne.symm, hnot_ch q (by rw [hpq]; simp)⟩
      · exact ⟨hlt, p, Or.inr hpq, hp, hne, hnot_ch p (by rw [hpq]; simp)⟩
    have hand_z_true : ∀ (v : Fin n) (hv : v ∉ Tbranch) (u : Fin n), G.Adj v u →
        ∀ (hlt : nextOf (orEnd v.val) < C.gates.length) (z : ℕ),
          ((C.gates[nextOf (orEnd v.val)]'hlt).inputs = [orEnd v.val, z] ∨
           (C.gates[nextOf (orEnd v.val)]'hlt).inputs = [z, orEnd v.val]) →
          z < n + nextOf (orEnd v.val) → z ≠ orEnd v.val → z ∉ orChain v.val →
          (C.wires (List.ofFn (fun t : Fin n => decide (t = u)))).getD z false = true := by
      intro v hv u hvu hlt z hord hzlt hzne hzch
      obtain ⟨h1, _, hand⟩ := hand_exit v hv
      have hvu_ne : v ≠ u := G.ne_of_adj hvu
      let x : Fin n → Bool := fun t => decide (t = u)
      let y : Fin n → Bool := Function.update x v true
      have hzeq : (C.wires (List.ofFn x)).getD z false = (C.wires (List.ofFn y)).getD z false := by
        have hrec : ∀ w < n + nextOf (orEnd v.val), w ∉ orChain v.val → w ≠ orEnd v.val →
            (C.wires (List.ofFn x)).getD w false = (C.wires (List.ofFn y)).getD w false := by
          intro w
          induction w using Nat.strong_induction_on with
          | ind w ihw =>
            intro hwlt hwch hwne
            by_cases hw1 : w < n
            · rw [wires_input C x w hw1, wires_input C y w hw1]
              have hne : (⟨w, hw1⟩ : Fin n) ≠ v := by
                intro h
                have hwv : w = v.val := congrArg Fin.val h
                subst hwv
                rcases horChain_self_or v.val (by omega) with hm | he
                · exact hwch hm
                · exact hwne he
              exact (Function.update_of_ne hne true x).symm
            · have hjlt : w - n < C.gates.length := by have : C.gates.length = s := hCsize; omega
              set j := w - n
              have hwj : w = n + j := by omega
              have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
              rw [hwj, wires_gate_ofFn C x j _ hg, wires_gate_ofFn C y j _ hg]
              congr 1
              apply List.map_congr_left
              intro k hk
              by_cases hklt : k < n + j
              · simp only [hklt, ↓reduceIte]
                apply ihw k (by omega) (by omega)
                · intro hkch
                  obtain ⟨_, hklt1, hk1, hknxt⟩ := (horChain_props v.val (by omega)).2 k hkch
                  obtain ⟨_, _, huniq⟩ := hnextOf_spec k hklt1 hk1
                  have hjeq : j = nextOf k := huniq ⟨j, hjlt⟩ hk
                  rw [hjeq] at hwj
                  rcases hknxt with h1' | h2'
                  · exact hwch (hwj ▸ h1')
                  · exact hwne (hwj ▸ h2')
                · intro hks
                  subst hks
                  obtain ⟨_, _, huniq⟩ := hnextOf_spec (orEnd v.val) (hs_ne_out v) h1
                  have hjeq : j = nextOf (orEnd v.val) := huniq ⟨j, hjlt⟩ hk
                  omega
              · simp only [hklt, ↓reduceIte]
        exact hrec z hzlt hzch hzne
      by_contra hzf
      have hz0 : (C.wires (List.ofFn x)).getD z false = false := by
        cases h : (C.wires (List.ofFn x)).getD z false
        · rfl
        · exact absurd h hzf
      have hz0' : (C.wires (List.ofFn y)).getD z false = false := hzeq.symm.trans hz0
      have hg : C.gates[nextOf (orEnd v.val)]? = some (C.gates[nextOf (orEnd v.val)]'hlt) := List.getElem?_eq_getElem hlt
      have ha0 : (C.wires (List.ofFn x)).getD (n + nextOf (orEnd v.val)) false = false := by
        rw [wires_gate_ofFn C x _ _ hg, hand]
        rcases hord with h | h <;> rw [h] <;> simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, hzlt, ↓reduceIte, hz0, Bool.false_and, Bool.and_false]
      have ha0' : (C.wires (List.ofFn y)).getD (n + nextOf (orEnd v.val)) false = false := by
        rw [wires_gate_ofFn C y _ _ hg, hand]
        rcases hord with h | h <;> rw [h] <;> simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, hzlt, ↓reduceIte, hz0', Bool.false_and, Bool.and_false]
      have hout_ch : C.output ∉ orChain v.val := fun hm => by
        have := (horChain_props v.val (by omega)).2 C.output hm; omega
      have hout_ne : C.output ≠ orEnd v.val := by have := hs_ne_out v; omega
      have heval := hand_sole_exit v hv x y (fun t ht => (Function.update_of_ne ht true x).symm)
        (ha0.trans ha0'.symm) C.output (by omega) hout_ch hout_ne
      change C.eval (List.ofFn x) = C.eval (List.ofFn y) at heval
      have hf0 : C.eval (List.ofFn x) = false := by
        cases h : C.eval (List.ofFn x) with
        | false => rfl
        | true =>
          obtain ⟨a, b, hab, ha, hb⟩ := negative _ ⟨u, u, by simp [x]⟩ ((hfun x).mp h)
          simp only [x, decide_eq_true_eq] at ha hb
          subst ha; subst hb; exact absurd hab (G.loopless.irrefl _)
      have hf1 : C.eval (List.ofFn y) = true := by
        rw [hfun]
        apply positive
        exact ⟨v, u, hvu, by simp [y], by simp [y, x, hvu_ne.symm]⟩
      rw [hf0, hf1] at heval; exact absurd heval (by decide)
    have hvc : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G Tbranch := by
      intro v w hvw
      by_contra hneither
      have hv : v ∉ Tbranch := fun h => hneither (Or.inl h)
      have hw : w ∉ Tbranch := fun h => hneither (Or.inr h)
      have hvw_ne : v ≠ w := G.ne_of_adj hvw
      have hstep_le : ∀ (a b : Fin n) (ha : a ∉ Tbranch) (hb : b ∉ Tbranch),
          G.Adj a b → nextOf (orEnd a.val) ≤ nextOf (orEnd b.val) → False := by
        intro a b ha hb hab hle
        have hab_ne : a ≠ b := G.ne_of_adj hab
        obtain ⟨hlta, za, horda, hzalt, hzane, hzach⟩ := hother_input_and a ha
        obtain ⟨h1a, _, handa⟩ := hand_exit a ha
        obtain ⟨h1b, hltb, handb⟩ := hand_exit b hb
        by_cases heq_gate : nextOf (orEnd a.val) = nextOf (orEnd b.val)
        · obtain ⟨hltb', hmemb, _⟩ := hnextOf_spec (orEnd b.val) (hs_ne_out b) h1b
          have hmemb' : orEnd b.val ∈ (C.gates[nextOf (orEnd a.val)]'hlta).inputs := by
            simpa only [heq_gate] using hmemb
          have hza_eq : za = orEnd b.val := by
            rcases horda with h | h <;> rw [h] at hmemb' <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hmemb'
            · rcases hmemb' with h' | h'
              · exact absurd (hs_inj h'.symm) hab_ne
              · exact h'.symm
            · rcases hmemb' with h' | h'
              · exact h'.symm
              · exact absurd (hs_inj h'.symm) hab_ne
          have hpos : 1 < (G.neighborFinset a).card := by have := degree a; change 2 ≤ (G.neighborFinset a).card at this; omega
          obtain ⟨u1, hu1, u2, hu2, hu12⟩ := Finset.one_lt_card.mp hpos
          obtain ⟨u, hua, hub⟩ : ∃ u : Fin n, G.Adj a u ∧ u ≠ b := by
            by_cases h1 : u1 = b
            · exact ⟨u2, (SimpleGraph.mem_neighborFinset G a u2).mp hu2, fun h => hu12 (h1.trans h.symm)⟩
            · exact ⟨u1, (SimpleGraph.mem_neighborFinset G a u1).mp hu1, h1⟩
          have hzt := hand_z_true a ha u hua hlta za horda hzalt hzane hzach
          rw [hza_eq] at hzt
          have hz0 := hs_zero_other b u hub
          rw [hz0] at hzt; exact absurd hzt (by decide)
        · have hlt_ab : nextOf (orEnd a.val) < nextOf (orEnd b.val) := by omega
          have hzt := hand_z_true a ha b hab hlta za horda hzalt hzane hzach
          have hza_not_sb : za ≠ orEnd b.val := by
            intro h
            subst h
            obtain ⟨_, _, huniq⟩ := hnextOf_spec (orEnd b.val) (hs_ne_out b) h1b
            have hmemza : orEnd b.val ∈ (C.gates[nextOf (orEnd a.val)]'hlta).inputs := by
              rcases horda with h1 | h1 <;> rw [h1] <;> simp
            exact heq_gate (huniq ⟨nextOf (orEnd a.val), hlta⟩ hmemza)
          have hza_not_chb : za ∉ orChain b.val := by
            intro hch
            obtain ⟨_, zlt1, z1, hznxt⟩ := (horChain_props b.val (by omega)).2 za hch
            obtain ⟨_, _, huniq⟩ := hnextOf_spec za zlt1 z1
            have hmemza : za ∈ (C.gates[nextOf (orEnd a.val)]'hlta).inputs := by
              rcases horda with h1 | h1 <;> rw [h1] <;> simp
            have heq : nextOf (orEnd a.val) = nextOf za := huniq ⟨nextOf (orEnd a.val), hlta⟩ hmemza
            have hgt_b := horChain_props b.val (by omega)
            have hlt_sb : n + nextOf za ≤ orEnd b.val := by
              rcases hznxt with h1' | h2'
              · exact le_of_lt (hgt_b.2 _ h1').1
              · exact le_of_eq h2'
            have hlt_a' : orEnd a.val < n + nextOf (orEnd a.val) := hnextOf_gt _ (hs_ne_out a) h1a
            have hlt_b' : orEnd b.val < n + nextOf (orEnd b.val) := hnextOf_gt _ (hs_ne_out b) h1b
            have hba_lt : nextOf (orEnd a.val) < C.gates.length := hlta
            have hnot_and : (C.gates[nextOf za]'(heq ▸ hlta)).op = GateOp.or := by
              have hzprops : ∀ w0, w0 < n + s → ∀ u ∈ orChain w0,
                  ∃ hlt' : nextOf u < C.gates.length, (C.gates[nextOf u]'hlt').op = GateOp.or := by
                intro w0 hw0
                induction hrem : n + s - w0 using Nat.strong_induction_on generalizing w0 with
                | ind rem ihr =>
                  intro u hu
                  dsimp only [orChain] at hu; rw [orChainAux] at hu
                  split_ifs at hu with h' hlt'
                  · cases hop' : (C.gates[nextOf w0]'hlt').op with
                    | or =>
                      rw [hop'] at hu
                      rcases Finset.mem_insert.mp hu with rfl | hu'
                      · exact ⟨hlt', hop'⟩
                      · have hgt := hnextOf_gt w0 h'.1 h'.2
                        have hns : nextOf w0 < s := by omega
                        exact ihr (n + s - (n + nextOf w0)) (by omega) (n + nextOf w0) (by omega) rfl u hu'
                    | and => rw [hop'] at hu; simp at hu
                    | not => rw [hop'] at hu; simp at hu
                    | mod _ => rw [hop'] at hu; simp at hu
                    | maj => rw [hop'] at hu; simp at hu
                  · simp at hu
                  · simp at hu
              obtain ⟨_, hor'⟩ := hzprops b.val (by omega) za hch
              exact hor'
            have : (C.gates[nextOf (orEnd a.val)]'hlta).op = GateOp.or := by simpa [heq] using hnot_and
            rw [handa] at this; cases this
          have hza_indep_b : ∀ u < n + nextOf (orEnd b.val), u ∉ orChain b.val → u ≠ orEnd b.val →
              (C.wires (List.ofFn (fun _ : Fin n => false))).getD u false =
              (C.wires (List.ofFn (fun t : Fin n => decide (t = b)))).getD u false := by
            intro u
            induction u using Nat.strong_induction_on with
            | ind u ihu =>
              intro hult huch hune
              by_cases hu1 : u < n
              · rw [wires_input C _ u hu1, wires_input C _ u hu1]
                have hne : (⟨u, hu1⟩ : Fin n) ≠ b := by
                  intro h
                  have hub : u = b.val := congrArg Fin.val h
                  subst hub
                  rcases horChain_self_or b.val (by omega) with hm | he
                  · exact huch hm
                  · exact hune he
                simp [hne]
              · have hjlt : u - n < C.gates.length := by have : C.gates.length = s := hCsize; omega
                set j := u - n
                have huj : u = n + j := by omega
                have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
                rw [huj, wires_gate_ofFn C _ j _ hg, wires_gate_ofFn C _ j _ hg]
                congr 1
                apply List.map_congr_left
                intro k hk
                by_cases hklt : k < n + j
                · simp only [hklt, ↓reduceIte]
                  apply ihu k (by omega) (by omega)
                  · intro hkch
                    obtain ⟨_, hklt1, hk1, hknxt⟩ := (horChain_props b.val (by omega)).2 k hkch
                    obtain ⟨_, _, huniq⟩ := hnextOf_spec k hklt1 hk1
                    have hjeq : j = nextOf k := huniq ⟨j, hjlt⟩ hk
                    rw [hjeq] at huj
                    rcases hknxt with h1' | h2'
                    · exact huch (huj ▸ h1')
                    · exact hune (huj ▸ h2')
                  · intro hks
                    subst hks
                    obtain ⟨_, _, huniq⟩ := hnextOf_spec (orEnd b.val) (hs_ne_out b) h1b
                    have hjeq : j = nextOf (orEnd b.val) := huniq ⟨j, hjlt⟩ hk
                    omega
                · simp only [hklt, ↓reduceIte]
          have hza0 : (C.wires (List.ofFn (fun _ : Fin n => false))).getD za false = true :=
            (hza_indep_b za (by omega) hza_not_chb hza_not_sb).trans hzt
          have hza_all : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD za false = true := fun x =>
            wires_mono C hmono (fun _ => false) x (fun _ h => absurd h (by decide)) za hza0
          have ha_copy : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + nextOf (orEnd a.val)) false =
              (C.wires (List.ofFn x)).getD (orEnd a.val) false := by
            intro x
            have hg : C.gates[nextOf (orEnd a.val)]? = some (C.gates[nextOf (orEnd a.val)]'hlta) := List.getElem?_eq_getElem hlta
            have hs_lt : orEnd a.val < n + nextOf (orEnd a.val) := hnextOf_gt _ (hs_ne_out a) h1a
            rw [wires_gate_ofFn C x _ _ hg, handa]
            rcases horda with h1 | h1 <;> rw [h1] <;> simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, hs_lt, hzalt, ↓reduceIte, hza_all x, Bool.true_and, Bool.and_true]
          have hja_s : nextOf (orEnd a.val) < s := by omega
          exact (hno_const_or_copy (nextOf (orEnd a.val)) hja_s).2.2 (orEnd a.val) (hnextOf_gt _ (hs_ne_out a) h1a) ha_copy
      rcases le_total (nextOf (orEnd v.val)) (nextOf (orEnd w.val)) with hle | hle
      · exact hstep_le v w hv hw hvw hle
      · exact hstep_le w v hw hv hvw.symm hle
    have ht_le_T : t ≤ Tbranch.card := ht_min Tbranch hvc
    set Simg : Finset ℕ := Tbranch.image (fun v : Fin n => orEnd v.val)
    have hSimg_sub : Simg ⊆ Finset.range (n + s - 1) := by
      intro w hw
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hw
      exact Finset.mem_range.mpr (hs_ne_out v)
    have hSimg_card : Simg.card = Tbranch.card := Finset.card_image_of_injective Tbranch hs_inj
    have hsum_ge_T : Tbranch.card ≤ ∑ w ∈ Simg, (outdeg w - 1) := by
      have hle1 : ∀ w ∈ Simg, 1 ≤ outdeg w - 1 := by
        intro w hw
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
        have := (Finset.mem_filter.mp hv).2
        omega
      have := Finset.sum_le_sum hle1
      simp only [Finset.sum_const, smul_eq_mul, mul_one, hSimg_card] at this
      exact this
    have hsum_le_all : ∑ w ∈ Simg, (outdeg w - 1) ≤ ∑ w ∈ Finset.range (n + s - 1), (outdeg w - 1) :=
      Finset.sum_le_sum_of_subset hSimg_sub
    have hs_eq : s = n + t - 1 := by omega
    have hT_eq : Tbranch.card = t := by omega
    have houtdeg_eq2 : ∀ w ∈ Simg, outdeg w = 2 := by
      intro w hw
      have hge2 : 2 ≤ outdeg w := by
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
        exact (Finset.mem_filter.mp hv).2
      by_contra hne2
      have hgt1 : 1 < outdeg w - 1 := by omega
      have hstrict : ∑ _u ∈ Simg, 1 < ∑ u ∈ Simg, (outdeg u - 1) :=
        Finset.sum_lt_sum (fun u hu => by
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
          have := (Finset.mem_filter.mp hv).2; omega) ⟨w, hw, hgt1⟩
      simp only [Finset.sum_const, smul_eq_mul, mul_one, hSimg_card] at hstrict
      omega
    have houtdeg_eq1_outside : ∀ w < n + s - 1, w ∉ Simg → outdeg w = 1 := by
      intro w hw hwNot
      have hge1 := houtdeg_ge1 w hw
      by_contra hne1
      have hpos : 0 < outdeg w - 1 := by omega
      have hadd : (∑ u ∈ Simg, (outdeg u - 1)) + (outdeg w - 1) ≤ ∑ u ∈ Finset.range (n + s - 1), (outdeg u - 1) := by
        have hsub2 : insert w Simg ⊆ Finset.range (n + s - 1) :=
          Finset.insert_subset (Finset.mem_range.mpr hw) hSimg_sub
        have := Finset.sum_le_sum_of_subset (f := fun u => outdeg u - 1) hsub2
        rw [Finset.sum_insert hwNot] at this
        omega
      omega
    set I : Finset (Fin n) := Finset.univ \ Tbranch
    have hI_card : I.card = n - t := by
      have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ Tbranch)
      change I.card + Tbranch.card = (Finset.univ : Finset (Fin n)).card at this
      simp only [Finset.card_univ, Fintype.card_fin, hT_eq] at this
      omega
    have hT_nbr_I : ∀ v ∈ Tbranch, 3 ≤ G.degree v → (G.neighborFinset v ∩ I).card ≤ 1 := by
      intro v hv hThree
      let ev : Fin n → Bool := fun t => decide (t = v)
      set Tv : Finset ℕ := (Finset.range (n + s)).filter (fun w => (C.wires (List.ofFn ev)).getD w false = true)
      have hv_in_Tv : v.val ∈ Tv := by
        rw [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, ?_⟩
        rw [wires_input C ev v.val v.isLt]; simp [ev]
      have hsv_in_Tv : orEnd v.val ∈ Tv := by
        rw [Finset.mem_filter, Finset.mem_range]
        refine ⟨by have := hs_ne_out v; omega, ?_⟩
        apply horEnd_true v.val ev (by omega)
        rw [wires_input C ev v.val v.isLt]; simp [ev]
      have hout_not_Tv : n + s - 1 ∉ Tv := by
        intro hm
        have ht := (Finset.mem_filter.mp hm).2
        rw [← hout_last] at ht
        change C.eval (List.ofFn ev) = true at ht
        obtain ⟨a, b, hab, ha, hb⟩ := negative _ ⟨v, v, by simp [ev]⟩ ((hfun ev).mp ht)
        simp only [ev, decide_eq_true_eq] at ha hb
        subst ha; subst hb; exact G.loopless.irrefl _ hab
      have hTv_lt : ∀ w ∈ Tv, w < n + s - 1 := by
        intro w hw
        have hlt := Finset.mem_range.mp (Finset.mem_filter.mp hw).1
        have hne : w ≠ n + s - 1 := fun h => hout_not_Tv (h ▸ hw)
        omega
      have hTv_outdeg : ∀ w ∈ Tv, outdeg w = if w = orEnd v.val then 2 else 1 := by
        intro w hw
        by_cases heq : w = orEnd v.val
        · simp only [heq, ↓reduceIte]
          exact houtdeg_eq2 _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
        · simp only [heq, ↓reduceIte]
          apply houtdeg_eq1_outside w (hTv_lt w hw)
          intro hS
          obtain ⟨v', _, hv'eq⟩ := Finset.mem_image.mp hS
          have hv'ne : v' ≠ v := fun h => heq (hv'eq.symm.trans (congrArg (fun x : Fin n => orEnd x.val) h))
          have h0 := hs_zero_other v' v hv'ne.symm
          have h1 := (Finset.mem_filter.mp hw).2
          rw [← hv'eq, h0] at h1
          exact absurd h1 (by decide)
      have hsum_Tv_outdeg : ∑ w ∈ Tv, outdeg w = Tv.card + 1 := by
        have hrew : ∑ w ∈ Tv, outdeg w = ∑ w ∈ Tv, (if w = orEnd v.val then 2 else 1) :=
          Finset.sum_congr rfl hTv_outdeg
        rw [hrew, ← Finset.add_sum_erase _ _ hsv_in_Tv]
        simp only [↓reduceIte]
        have hrest : ∑ w ∈ Tv.erase (orEnd v.val), (if w = orEnd v.val then 2 else 1) = (Tv.erase (orEnd v.val)).card := by
          trans ∑ _w ∈ Tv.erase (orEnd v.val), 1
          · apply Finset.sum_congr rfl
            intro w hw; simp [(Finset.mem_erase.mp hw).1]
          · simp
        rw [hrest]
        have := Finset.card_erase_add_one hsv_in_Tv
        omega
      let Ev : Finset (Fin C.gates.length) :=
        Finset.univ.filter (fun j : Fin C.gates.length => n + j.val ∉ Tv ∧ ∃ i ∈ (C.gates[j.val]).inputs, i ∈ Tv)
      have hmem_Ev : ∀ j : Fin C.gates.length, j ∈ Ev ↔ n + j.val ∉ Tv ∧ ∃ i ∈ (C.gates[j.val]'j.isLt).inputs, i ∈ Tv := fun j => by
        simp only [Ev, Finset.mem_filter, Finset.mem_univ, true_and]
      have hEv_le2 : Ev.card ≤ 2 := by
        let din : ℕ → ℕ := fun w => (Finset.univ.filter (fun j : Fin C.gates.length => n + j.val ∈ Tv ∧ w ∈ (C.gates[j.val]).inputs)).card
        let dout : ℕ → ℕ := fun w => (Finset.univ.filter (fun j : Fin C.gates.length => n + j.val ∉ Tv ∧ w ∈ (C.gates[j.val]).inputs)).card
        have hsplit : ∀ w, din w + dout w = outdeg w := by
          intro w
          rw [houtdeg_card]
          have := Finset.card_filter_add_card_filter_not (s := Finset.univ.filter (fun j : Fin C.gates.length => w ∈ (C.gates[j.val]).inputs))
            (p := fun j : Fin C.gates.length => n + j.val ∈ Tv)
          simpa only [din, dout, Finset.filter_filter, and_comm] using this
        have hdin_sum : Tv.card - 1 ≤ ∑ w ∈ Tv, din w := by
          have hswap : ∑ w ∈ Tv, din w =
              ∑ j ∈ Finset.univ.filter (fun j : Fin C.gates.length => n + j.val ∈ Tv),
                (Tv.filter (fun w => w ∈ (C.gates[j.val]).inputs)).card := by
            simp only [din, Finset.card_eq_sum_ones]
            have h1 : ∀ j : Fin C.gates.length,
                (∑ w ∈ Tv, if n + j.val ∈ Tv ∧ w ∈ (C.gates[j.val]).inputs then 1 else 0) =
                if n + j.val ∈ Tv then (Tv.filter (fun w => w ∈ (C.gates[j.val]).inputs)).card else 0 := by
              intro j
              by_cases hj : n + j.val ∈ Tv
              · simp [hj, Finset.sum_boole]
              · simp [hj]
            trans ∑ j : Fin C.gates.length, ∑ w ∈ Tv, if n + j.val ∈ Tv ∧ w ∈ (C.gates[j.val]).inputs then 1 else 0
            · rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro w _; simp only [Finset.sum_filter]
            · trans ∑ j : Fin C.gates.length, if n + j.val ∈ Tv then (Tv.filter (fun w => w ∈ (C.gates[j.val]).inputs)).card else 0
              · exact Finset.sum_congr rfl (fun j _ => h1 j)
              · rw [← Finset.sum_filter]; simp only [Finset.card_eq_sum_ones]
          rw [hswap]
          have hge1 : ∀ j ∈ Finset.univ.filter (fun j : Fin C.gates.length => n + j.val ∈ Tv),
              1 ≤ (Tv.filter (fun w => w ∈ (C.gates[j.val]).inputs)).card := by
            intro j hj
            have hjTv : n + j.val ∈ Tv := (Finset.mem_filter.mp hj).2
            have hjt : (C.wires (List.ofFn ev)).getD (n + j.val) false = true := (Finset.mem_filter.mp hjTv).2
            have hg : C.gates[j.val]? = some (C.gates[j.val]'j.isLt) := List.getElem?_eq_getElem j.isLt
            obtain ⟨p, q, hpq, hp, hq, _⟩ := hgate_shape j.val j.isLt
            have hgop : (C.gates[j.val]'j.isLt).op = GateOp.and ∨ (C.gates[j.val]'j.isLt).op = GateOp.or := by
              simpa using (hmono _ (List.getElem_mem j.isLt)).1
            rw [wires_gate_ofFn C ev j.val _ hg, hpq] at hjt
            have hex : (C.wires (List.ofFn ev)).getD p false = true ∨ (C.wires (List.ofFn ev)).getD q false = true := by
              rcases hgop with hand | hor
              · rw [hand] at hjt; simp [GateOp.eval, hp, hq] at hjt; exact Or.inl hjt.1
              · rw [hor] at hjt; simp [GateOp.eval, hp, hq] at hjt; exact hjt
            have hjs : j.val < s := by have := j.isLt; omega
            rcases hex with hpt | hqt
            · exact Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hpt⟩, by rw [hpq]; simp⟩⟩
            · exact Finset.card_pos.mpr ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hqt⟩, by rw [hpq]; simp⟩⟩
          have hsum_j := Finset.sum_le_sum hge1
          simp only [Finset.sum_const, smul_eq_mul, mul_one] at hsum_j
          have hcard_j : Tv.card - 1 ≤ (Finset.univ.filter (fun j : Fin C.gates.length => n + j.val ∈ Tv)).card := by
            have hsub_inj : (Tv.erase v.val).card ≤ (Finset.univ.filter (fun j : Fin C.gates.length => n + j.val ∈ Tv)).card := by
              refine Finset.card_le_card_of_injOn
                (fun w => if h : w - n < C.gates.length then ⟨w - n, h⟩ else ⟨0, by omega⟩) ?_ ?_
              · intro w hw
                have hwTv := Finset.mem_of_mem_erase hw
                have hne_v := (Finset.mem_erase.mp hw).1
                have hw_lt := hTv_lt w hwTv
                have hge_n : n ≤ w := by
                  by_contra hlt
                  have hwt := (Finset.mem_filter.mp hwTv).2
                  rw [wires_input C ev w (by omega)] at hwt
                  simp only [ev, decide_eq_true_eq] at hwt
                  exact hne_v (congrArg Fin.val hwt)
                have hsub_lt : w - n < C.gates.length := by omega
                simp only [hsub_lt, ↓reduceDIte, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
                rwa [show n + (w - n) = w by omega]
              · intro w1 hw1 w2 hw2 heq
                have h1Tv := Finset.mem_of_mem_erase hw1
                have h2Tv := Finset.mem_of_mem_erase hw2
                have hw1_lt := hTv_lt w1 h1Tv
                have hw2_lt := hTv_lt w2 h2Tv
                have hge1 : n ≤ w1 := by
                  by_contra hlt
                  have hwt := (Finset.mem_filter.mp h1Tv).2
                  rw [wires_input C ev w1 (by omega)] at hwt
                  simp only [ev, decide_eq_true_eq] at hwt
                  exact (Finset.mem_erase.mp hw1).1 (congrArg Fin.val hwt)
                have hge2 : n ≤ w2 := by
                  by_contra hlt
                  have hwt := (Finset.mem_filter.mp h2Tv).2
                  rw [wires_input C ev w2 (by omega)] at hwt
                  simp only [ev, decide_eq_true_eq] at hwt
                  exact (Finset.mem_erase.mp hw2).1 (congrArg Fin.val hwt)
                have hlt1 : w1 - n < C.gates.length := by omega
                have hlt2 : w2 - n < C.gates.length := by omega
                simp only [hlt1, hlt2, ↓reduceDIte] at heq
                have hv_eq : w1 - n = w2 - n := congrArg Fin.val heq
                omega
            have := Finset.card_erase_add_one hv_in_Tv
            omega
          omega
        have hdout_ge : Ev.card ≤ ∑ w ∈ Tv, dout w := by
          have hswap : ∑ w ∈ Tv, dout w =
              ∑ j ∈ Ev, (Tv.filter (fun w => w ∈ (C.gates[j.val]).inputs)).card := by
            trans ∑ j : Fin C.gates.length, ∑ w ∈ Tv, if n + j.val ∉ Tv ∧ w ∈ (C.gates[j.val]).inputs then 1 else 0
            · rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro w _; simp [dout]
            · rw [← Finset.sum_subset (Finset.subset_univ Ev)]
              · apply Finset.sum_congr rfl
                intro j hj
                have hjnot : n + j.val ∉ Tv := ((hmem_Ev j).mp hj).1
                simp [hjnot, Finset.sum_boole]
              · intro j _ hjnot
                simp only [Ev, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_exists] at hjnot
                by_cases hntv : n + j.val ∉ Tv
                · apply Finset.sum_eq_zero
                  intro w hw
                  have : w ∉ (C.gates[j.val]).inputs := fun hm => hjnot hntv w hm hw
                  simp [hntv, this]
                · simp [hntv]
          rw [hswap]
          have hge1 : ∀ j ∈ Ev, 1 ≤ (Tv.filter (fun w => w ∈ (C.gates[j.val]).inputs)).card := by
            intro j hj
            obtain ⟨i, hi_mem, hi_Tv⟩ := ((hmem_Ev j).mp hj).2
            exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi_Tv, hi_mem⟩⟩
          have := Finset.sum_le_sum hge1
          simpa using this
        have htot : (∑ w ∈ Tv, din w) + (∑ w ∈ Tv, dout w) = ∑ w ∈ Tv, outdeg w := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun w _ => hsplit w)
        have hTv_pos : 1 ≤ Tv.card := Finset.card_pos.mpr ⟨v.val, hv_in_Tv⟩
        omega
      have hu_maps_Ev : ∀ u ∈ G.neighborFinset v ∩ I,
          ∃ hlt : nextOf (orEnd u.val) < C.gates.length, (⟨nextOf (orEnd u.val), hlt⟩ : Fin C.gates.length) ∈ Ev := by
        intro u hu
        have hvu : G.Adj v u := (SimpleGraph.mem_neighborFinset G v u).mp (Finset.mem_inter.mp hu).1
        have huNotT : u ∉ Tbranch := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hu).2).2
        obtain ⟨hlt, z, hord, hzlt, hzne, hzch⟩ := hother_input_and u huNotT
        obtain ⟨_, _, handu⟩ := hand_exit u huNotT
        have hzt : (C.wires (List.ofFn ev)).getD z false = true :=
          hand_z_true u huNotT v hvu.symm hlt z hord hzlt hzne hzch
        have hsu0 : (C.wires (List.ofFn ev)).getD (orEnd u.val) false = false :=
          hs_zero_other u v (G.ne_of_adj hvu)
        have ha0 : (C.wires (List.ofFn ev)).getD (n + nextOf (orEnd u.val)) false = false := by
          have hg : C.gates[nextOf (orEnd u.val)]? = some (C.gates[nextOf (orEnd u.val)]'hlt) := List.getElem?_eq_getElem hlt
          have h1u := (hand_exit u huNotT).1
          have hsult : orEnd u.val < n + nextOf (orEnd u.val) := hnextOf_gt _ (hs_ne_out u) h1u
          rw [wires_gate_ofFn C ev _ _ hg, handu]
          rcases hord with h | h <;> rw [h] <;>
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, hsult, ↓reduceIte, hsu0, Bool.false_and, Bool.and_false]
        refine ⟨hlt, (hmem_Ev ⟨nextOf (orEnd u.val), hlt⟩).mpr ⟨?_, z, ?_, ?_⟩⟩
        · intro hm
          have h1 := (Finset.mem_filter.mp hm).2
          rw [ha0] at h1; exact absurd h1 (by decide)
        · rcases hord with h | h <;> rw [h] <;> simp
        · have hj_s : nextOf (orEnd u.val) < s := by omega
          exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hzt⟩
      have hu_inj : ∀ u1 ∈ G.neighborFinset v ∩ I, ∀ u2 ∈ G.neighborFinset v ∩ I,
          nextOf (orEnd u1.val) = nextOf (orEnd u2.val) → u1 = u2 := by
        intro u1 hu1 u2 hu2 heq
        have hvu1 : G.Adj v u1 := (SimpleGraph.mem_neighborFinset G v u1).mp (Finset.mem_inter.mp hu1).1
        have hvu2 : G.Adj v u2 := (SimpleGraph.mem_neighborFinset G v u2).mp (Finset.mem_inter.mp hu2).1
        have hu1NotT : u1 ∉ Tbranch := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hu1).2).2
        have hu2NotT : u2 ∉ Tbranch := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hu2).2).2
        obtain ⟨hlt1, z1, hord1, hz1lt, hz1ne, hz1ch⟩ := hother_input_and u1 hu1NotT
        have hz1t : (C.wires (List.ofFn ev)).getD z1 false = true :=
          hand_z_true u1 hu1NotT v hvu1.symm hlt1 z1 hord1 hz1lt hz1ne hz1ch
        have hsu20 : (C.wires (List.ofFn ev)).getD (orEnd u2.val) false = false :=
          hs_zero_other u2 v (G.ne_of_adj hvu2)
        have h1u2 := (hand_exit u2 hu2NotT).1
        obtain ⟨_, hm2, _⟩ := hnextOf_spec (orEnd u2.val) (hs_ne_out u2) h1u2
        have hm2' : orEnd u2.val ∈ (C.gates[nextOf (orEnd u1.val)]'hlt1).inputs := by
          simpa only [heq] using hm2
        rcases hord1 with h | h <;> rw [h] at hm2' <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2'
        · rcases hm2' with h' | h'
          · exact hs_inj h'.symm
          · rw [h', hz1t] at hsu20; exact absurd hsu20 (by decide)
        · rcases hm2' with h' | h'
          · rw [h', hz1t] at hsu20; exact absurd hsu20 (by decide)
          · exact hs_inj h'.symm
      have hcard_le2 : (G.neighborFinset v ∩ I).card ≤ 2 := by
        have hle := Finset.card_le_card_of_injOn
          (s := G.neighborFinset v ∩ I) (t := Ev)
          (fun u => if h : nextOf (orEnd u.val) < C.gates.length then ⟨nextOf (orEnd u.val), h⟩ else ⟨0, by omega⟩)
          (fun u hu => by
            obtain ⟨hlt, hmem⟩ := hu_maps_Ev u hu
            simp only [hlt, ↓reduceDIte, Finset.mem_coe]
            exact hmem)
          (fun u1 hu1 u2 hu2 heq => by
            have hlt1 := (hu_maps_Ev u1 hu1).1
            have hlt2 := (hu_maps_Ev u2 hu2).1
            simp only [hlt1, hlt2, ↓reduceDIte] at heq
            exact hu_inj u1 hu1 u2 hu2 (congrArg Fin.val heq))
        omega
      by_contra hgt1
      have hcard_eq2 : (G.neighborFinset v ∩ I).card = 2 := by omega
      rw [Finset.card_eq_two] at hcard_eq2
      obtain ⟨u1, u2, hu12, hN_I⟩ := hcard_eq2
      have hu1_in : u1 ∈ G.neighborFinset v ∩ I := hN_I ▸ by simp
      have hu2_in : u2 ∈ G.neighborFinset v ∩ I := hN_I ▸ by simp
      obtain ⟨hlt1, hEv1⟩ := hu_maps_Ev u1 hu1_in
      obtain ⟨hlt2, hEv2⟩ := hu_maps_Ev u2 hu2_in
      have hEv_ne : (⟨nextOf (orEnd u1.val), hlt1⟩ : Fin C.gates.length) ≠ ⟨nextOf (orEnd u2.val), hlt2⟩ :=
        fun h => hu12 (hu_inj u1 hu1_in u2 hu2_in (congrArg Fin.val h))
      have hEv_eq : Ev = {⟨nextOf (orEnd u1.val), hlt1⟩, ⟨nextOf (orEnd u2.val), hlt2⟩} := by
        symm
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        · rw [Finset.card_pair hEv_ne]; exact hEv_le2
      have hdegv : 3 ≤ (G.neighborFinset v).card := hThree
      have hdiff_pos : 0 < (G.neighborFinset v \ (G.neighborFinset v ∩ I)).card := by
        have h1 := Finset.card_sdiff_add_card_eq_card (Finset.inter_subset_left (s₁ := G.neighborFinset v) (s₂ := I))
        have h2 : (G.neighborFinset v ∩ I).card = 2 := by rw [hN_I, Finset.card_pair hu12]
        omega
      obtain ⟨v', hv'⟩ := Finset.card_pos.mp hdiff_pos
      have hvv' : G.Adj v v' := (SimpleGraph.mem_neighborFinset G v v').mp (Finset.mem_sdiff.mp hv').1
      have hv'not : v' ∉ G.neighborFinset v ∩ I := (Finset.mem_sdiff.mp hv').2
      have hv'ne1 : v' ≠ u1 := fun h => hv'not (h ▸ hu1_in)
      have hv'ne2 : v' ≠ u2 := fun h => hv'not (h ▸ hu2_in)
      have hvv'_ne : v ≠ v' := G.ne_of_adj hvv'
      let x0 : Fin n → Bool := fun t => decide (t = v')
      let x1 : Fin n → Bool := Function.update x0 v true
      have hnot_Tv_eq : ∀ w < n + s, w ∉ Tv →
          (C.wires (List.ofFn x0)).getD w false = (C.wires (List.ofFn x1)).getD w false := by
        intro w
        induction w using Nat.strong_induction_on with
        | ind w ihw =>
          intro hwlt hwNot
          by_cases hw1 : w < n
          · rw [wires_input C x0 w hw1, wires_input C x1 w hw1]
            have hne : (⟨w, hw1⟩ : Fin n) ≠ v := by
              intro h
              have hwv : w = v.val := congrArg Fin.val h
              exact hwNot (hwv ▸ hv_in_Tv)
            exact (Function.update_of_ne hne true x0).symm
          · have hjlt : w - n < C.gates.length := by have : C.gates.length = s := hCsize; omega
            set j := w - n
            have hwj : w = n + j := by omega
            by_cases hjEv : (⟨j, hjlt⟩ : Fin C.gates.length) ∈ Ev
            · rw [hEv_eq, Finset.mem_insert, Finset.mem_singleton] at hjEv
              have hand_zero : ∀ (uk : Fin n), uk ∈ G.neighborFinset v ∩ I → v' ≠ uk →
                  j = nextOf (orEnd uk.val) →
                  (C.wires (List.ofFn x0)).getD w false = (C.wires (List.ofFn x1)).getD w false := by
                intro uk huk hv'uk hjeq
                have huk_notT : uk ∉ Tbranch := (Finset.mem_sdiff.mp (Finset.mem_inter.mp huk).2).2
                have hvuk : G.Adj v uk := (SimpleGraph.mem_neighborFinset G v uk).mp (Finset.mem_inter.mp huk).1
                obtain ⟨h1uk, _, handuk⟩ := hand_exit uk huk_notT
                obtain ⟨_, hmem_su, _⟩ := hnextOf_spec (orEnd uk.val) (hs_ne_out uk) h1uk
                have hsu_lt : orEnd uk.val < n + j := by rw [hjeq]; exact hnextOf_gt _ (hs_ne_out uk) h1uk
                have hsu_not_Tv : orEnd uk.val ∉ Tv := by
                  intro hm
                  have h1 := (Finset.mem_filter.mp hm).2
                  have h0 := hs_zero_other uk v (G.ne_of_adj hvuk)
                  rw [h0] at h1; exact absurd h1 (by decide)
                have hsu_eq := ihw (orEnd uk.val) (by omega) (by omega) hsu_not_Tv
                have hsu_x0 : (C.wires (List.ofFn x0)).getD (orEnd uk.val) false = false :=
                  hs_zero_other uk v' hv'uk
                have hsu_x1 : (C.wires (List.ofFn x1)).getD (orEnd uk.val) false = false :=
                  hsu_eq.symm.trans hsu_x0
                have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
                have hgop : (C.gates[j]'hjlt).op = GateOp.and := by
                  simpa only [hjeq] using handuk
                have hmem_su' : orEnd uk.val ∈ (C.gates[j]'hjlt).inputs := by
                  simpa only [hjeq] using hmem_su
                have hf_and : ∀ y : Fin n → Bool, (C.wires (List.ofFn y)).getD (orEnd uk.val) false = false →
                    (C.wires (List.ofFn y)).getD w false = false := by
                  intro y hy0
                  rw [hwj, wires_gate_ofFn C y j _ hg, hgop]
                  change ((C.gates[j]'hjlt).inputs.map fun i => if i < n + j then (C.wires (List.ofFn y)).getD i false else false).all id = false
                  cases hv_all : ((C.gates[j]'hjlt).inputs.map fun i => if i < n + j then (C.wires (List.ofFn y)).getD i false else false).all id with
                  | false => rfl
                  | true =>
                    have ht := List.all_eq_true.mp hv_all _ (List.mem_map_of_mem hmem_su')
                    simp only [id_eq, hsu_lt, ↓reduceIte, hy0] at ht
                    exact absurd ht (by decide)
                exact (hf_and x0 hsu_x0).trans (hf_and x1 hsu_x1).symm
              rcases hjEv with h1 | h2
              · exact hand_zero u1 hu1_in hv'ne1 (congrArg Fin.val h1)
              · exact hand_zero u2 hu2_in hv'ne2 (congrArg Fin.val h2)
            · have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
              rw [hwj, wires_gate_ofFn C x0 j _ hg, wires_gate_ofFn C x1 j _ hg]
              congr 1
              apply List.map_congr_left
              intro i hi
              by_cases hilt : i < n + j
              · simp only [hilt, ↓reduceIte]
                have hiNot : i ∉ Tv := fun hiTv => hjEv ((hmem_Ev ⟨j, hjlt⟩).mpr ⟨hwj ▸ hwNot, i, hi, hiTv⟩)
                exact ihw i (by omega) (by omega) hiNot
              · simp only [hilt, ↓reduceIte]
      have heval := hnot_Tv_eq C.output (by omega) (hout_last ▸ hout_not_Tv)
      change C.eval (List.ofFn x0) = C.eval (List.ofFn x1) at heval
      have hf0 : C.eval (List.ofFn x0) = false := by
        cases h : C.eval (List.ofFn x0) with
        | false => rfl
        | true =>
          obtain ⟨a, b, hab, ha, hb⟩ := negative _ ⟨v', v', by simp [x0]⟩ ((hfun x0).mp h)
          simp only [x0, decide_eq_true_eq] at ha hb
          subst ha; subst hb; exact absurd hab (G.loopless.irrefl _)
      have hf1 : C.eval (List.ofFn x1) = true := by
        rw [hfun]
        apply positive
        exact ⟨v, v', hvv', by simp [x1], by simp [x1, x0, hvv'_ne.symm]⟩
      rw [hf0, hf1] at heval; exact absurd heval (by decide)
    obtain ⟨v, hv, deg, many⟩ := coverWitness Tbranch hvc hT_eq
    have few := hT_nbr_I v hv deg
    change 2 ≤ (G.neighborFinset v ∩ I).card at many
    omega

end SparseBranchBound

end PEqualNP.Outside.L_meta_4445

namespace PEqualNP.Outside.L_meta_4445.RawLower

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.CoverPromise

private abbrev G := PairBound.graph false

private instance graphAdj : DecidableRel G.Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ ((i,j) ∈ PairBound.edgeList false ∨
    (j,i) ∈ PairBound.edgeList false)))

private instance vertexCoverDec (S : Finset (Fin 9)) : Decidable (IsVertexCover G S) := by
  unfold IsVertexCover
  infer_instance

private theorem enoughNeighbors : ∀ v, 2 ≤ G.degree v := by decide +kernel

private theorem separation : ∀ v w, v ≠ w → ∃ u, G.Adj v u ∧ ¬G.Adj w u := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
private theorem coverBoundary : ∀ S : Finset (Fin 9), IsVertexCover G S → S.card = 5 →
    ∃ v ∈ S, 3 ≤ G.degree v ∧ 2 ≤ (G.neighborFinset v ∩ (Finset.univ \ S)).card := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
private theorem coverMinimum : ∀ S : Finset (Fin 9), IsVertexCover G S → 5 ≤ S.card := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 10000000 in
private theorem edgeEvaluation : ∀ x : Fin 9 → Bool, PairSemantics.target x = true ↔
    ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  decide +kernel

theorem lower (C : Circuit) (hm : Monotone2 C)
    (correct : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = PairSemantics.target x) :
    14 ≤ C.size := by
  have b := SparseBranchBound.main_bound 9 5 G enoughNeighbors separation coverBoundary
    (fun x => PairSemantics.target x = true)
    (fun x h => (edgeEvaluation x).2 h)
    (fun x _ h => (edgeEvaluation x).1 h)
    coverMinimum C.size C rfl hm (fun x => by rw [correct])
  exact b

end PEqualNP.Outside.L_meta_4445.RawLower

namespace PEqualNP.Outside.L_meta_4445

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem tripleImpossible (C : Circuit) (t : Fin 9)
    (ht : t = 0 ∨ t = 2 ∨ t = 7) (hm : Monotone2 C) (budget : C.size ≤ 13)
    (used : ∃ g ∈ C.gates, 9 ∈ g.inputs)
    (correct : ∀ x : Fin 9 → Bool,
      C.eval (List.ofFn x ++ [x 4 || x 6 || x t]) = PairSemantics.target x) : False := by
  let singleton : Fin 9 → Bool := fun i => decide (i = 4)
  let edge : Fin 9 → Bool := fun i => decide (i = 4 ∨ i = 0)
  have singleFlag : (singleton 4 || singleton 6 || singleton t) = true := by
    change ((true || singleton 6) || singleton t) = true
    rfl
  have edgeFlag : (edge 4 || edge 6 || edge t) = true := by
    change ((true || edge 6) || edge t) = true
    rfl
  have notConstant : ∃ x y : Fin 9 → Bool,
      C.eval (List.ofFn x ++ [true]) ≠ C.eval (List.ofFn y ++ [true]) := by
    refine ⟨singleton, edge, ?_⟩
    have hS := correct singleton
    have hE := correct edge
    rw [singleFlag] at hS
    rw [edgeFlag] at hE
    rw [hS, hE]
    decide +kernel
  obtain ⟨K, hmK, count, evalEq⟩ := PinTrue.apply C hm notConstant
  have saved := PinTrue.countPositive C used
  have lower : 13 ≤ K.size := by
    apply pairLower_of_monotone K t ht hmK
    · intro x hx
      rw [evalEq]
      apply PinTrue.intoTrue C hm x (x 4 || x 6 || x t)
      rwa [correct x]
    · intro x hx
      rw [evalEq]
      simpa only [hx] using correct x
  omega

end PEqualNP.Outside.L_meta_4445

namespace PEqualNP.Outside.L_meta_4445

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem maskAsTriple (m : Nat) (hm : m ∈ ([81,84,208] : List Nat)) :
    ∃ t : Fin 9, (t = 0 ∨ t = 2 ∨ t = 7) ∧
      ∀ x : Fin 9 → Bool, decide (∃ i : Fin 9, m.testBit i.val = true ∧ x i = true) =
        (x 4 || x 6 || x t) := by
  have cases : m = 81 ∨ m = 84 ∨ m = 208 := by simpa using hm
  rcases cases with rfl | rfl | rfl
  · exact ⟨0, Or.inl rfl, by decide +kernel⟩
  · exact ⟨2, Or.inr (Or.inl rfl), by decide +kernel⟩
  · exact ⟨7, Or.inr (Or.inr rfl), by decide +kernel⟩

theorem extraImpossible (D : Circuit) (small : D.size ≤ 13) (hm : Monotone2 D)
    (t : Fin 9) (ht : t = 0 ∨ t = 2 ∨ t = 7)
    (correct : ∀ x : Fin 9 → Bool,
      D.eval (List.ofFn x ++ [x 4 || x 6 || x t]) = PairSemantics.target x) : False := by
  classical
  by_cases used : ∃ g ∈ D.gates, 9 ∈ g.inputs
  · exact tripleImpossible D t ht hm small used correct
  · have same := PinTrue.hintUnused D t used correct
    let edge : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 1)
    have different : ∃ x y : Fin 9 → Bool,
        D.eval (List.ofFn x ++ [true]) ≠ D.eval (List.ofFn y ++ [true]) := by
      refine ⟨(fun _ => false), edge, ?_⟩
      rw [same, same]
      decide +kernel
    obtain ⟨K, monoK, bound, eqK⟩ := PinTrue.apply D hm different
    have stop := RawLower.lower K monoK (fun x => (eqK x).trans (same x))
    omega

end PEqualNP.Outside.L_meta_4445

theorem PEqualNP.Outside.L_meta_4445 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ x2 ∈ [(81 : ℕ), (84 : ℕ), (208 : ℕ)], ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → (∀ (x6 : Fin (9 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x4 (Fin.snoc (Fin.snoc x6 (x6 (4 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)))) (Decidable.decide (∃ (x7 : Fin (9 : ℕ)), x2.testBit ↑x7 = Bool.true ∧ x6 x7 = Bool.true))) = x1 x6) → (14 : ℕ) ≤ x4.size := by
  dsimp only
  intro m hm C fan computes
  by_contra bound
  obtain ⟨D, sizeD, monoD, raw | wired⟩ :=
    PEqualNP.Outside.L_meta_4445_aux.from_computing m hm C fan computes (by omega)
  · have h := PEqualNP.Outside.L_meta_4445.RawLower.lower D monoD raw
    omega
  · obtain ⟨t, ht, hmask⟩ := PEqualNP.Outside.L_meta_4445.maskAsTriple m hm
    apply PEqualNP.Outside.L_meta_4445.extraImpossible D sizeD monoD t ht
    intro x
    have eval := wired x
    rw [hmask x] at eval
    exact eval
