import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_11201

-- Compression des fils et restriction adaptées de L-meta-4425 et L-meta-2960.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


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

def Live (m : ℕ) : ℕ → Finset ℕ → Prop
  | 0, S => ∃ a, S = {a} ∧ Good m a ∧ a ≠ 0
  | k+1, S => ∃ (U : Finset ℕ) (a b d : ℕ),
      S = insert a (insert b U) ∧
      d < 4 ∧ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
      combine d a b ∉ insert a (insert b U) ∧
      Live m k (insert (combine d a b) U)

namespace Live

lemma done {m a : ℕ} (hg : Good m a) (nonzero : a ≠ 0) : Live m 0 {a} := by
  rw [Live]
  exact ⟨a, rfl, hg, nonzero⟩

lemma step {m k : ℕ} {U : Finset ℕ} {a b d : ℕ}
    (hd : d < 4) (ha : a ≠ 0) (hb : b ≠ 0) (diff : a ≠ b)
    (fresh : combine d a b ∉ insert a (insert b U))
    (next : Live m k (insert (combine d a b) U)) :
    Live m (k+1) (insert a (insert b U)) := by
  rw [Live]
  exact ⟨U, a, b, d, rfl, hd, ha, hb, diff, fresh, next⟩

end Live

lemma liveNonzero {m k S} (h : Live m k S) : ∀ a∈S,a≠0 := by
  induction k generalizing S with
  | zero =>
    rw [Live] at h
    obtain ⟨a, rfl, _, hn⟩ := h
    simpa using hn
  | succ k ih =>
    rw [Live] at h
    obtain ⟨U, a, b, d, rfl, _, ha, hb, _, _, tail⟩ := h
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact ha
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact hb
    exact ih tail x (Finset.mem_insert_of_mem hx)
lemma liveSize {m k S} (h : Live m k S) : S.card≤k+1 := by
  induction k generalizing S with
  | zero =>
    rw [Live] at h
    obtain ⟨a, rfl, _, _⟩ := h
    simp
  | succ k ih =>
    rw [Live] at h
    obtain ⟨U, a, b, d, rfl, _, _, _, _, fresh, tail⟩ := h
    have bound := ih tail
    have z : combine d a b ∉ U := fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    rw [Finset.card_insert_of_notMem z] at bound
    have u := Finset.card_insert_le a (insert b U)
    have v := Finset.card_insert_le b U
    omega
lemma combine_congr_bits (d a b i j : ℕ) (p : a.testBit i=a.testBit j) (q : b.testBit i=b.testBit j) :
    (combine d a b).testBit i=(combine d a b).testBit j := by
  rcases d with _|(_|(_|d)) <;> simp [combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,p,q]
lemma liveSeparates {m k S} (h : Live m k S) (i : ℕ) (hi : i<m) :
    ∃ a∈S,a.testBit i≠a.testBit (m+i) := by
  induction k generalizing S with
  | zero =>
    rw [Live] at h
    obtain ⟨a, rfl, hg, _⟩ := h
    exact ⟨a, Finset.mem_singleton_self a, hg i hi⟩
  | succ k ih =>
    rw [Live] at h
    obtain ⟨U, a, b, d, rfl, _, _, _, _, _, tail⟩ := h
    obtain ⟨x,hx,dist⟩ := ih tail
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
    cases n with
    | zero =>
      rw [Live] at h
      obtain ⟨a, rfl, hg, _⟩ := h
      exact ends hg v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self a))
    | succ n => omega
  | succ k ih =>
    rw [search,Bool.or_eq_true]
    cases n with
    | zero =>
      rw [Live] at h
      obtain ⟨a, rfl, hg, _⟩ := h
      exact Or.inl (ends hg v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self a)))
    | succ n =>
      rw [Live] at h
      obtain ⟨U, a, b, d, rfl, hd, _, _, ab, fresh, tail⟩ := h
      exact Or.inr (transition hd ab fresh rep nd (by omega) tail (fun v hv nv => ih tail (by omega) v hv nv))






abbrev Projection (m h : ℕ) := { f : ℕ → ℕ //
  f 0 = 0 ∧ (∀ d a b, d < 4 → f (combine d a b) = combine d (f a) (f b)) ∧
  (∀ a, Good m a → Good h (f a)) ∧ 0 < h }

namespace Projection
def toFun {m h : ℕ} (p : Projection m h) : ℕ → ℕ := p.val
theorem atZero {m h : ℕ} (p : Projection m h) : p.toFun 0 = 0 := p.property.1
theorem combineEq {m h : ℕ} (p : Projection m h) (d a b : ℕ) (hd : d < 4) :
    p.toFun (combine d a b) = combine d (p.toFun a) (p.toFun b) :=
  p.property.2.1 d a b hd
theorem good {m h : ℕ} (p : Projection m h) (a : ℕ) (ha : Good m a) :
    Good h (p.toFun a) := p.property.2.2.1 a ha
theorem someRow {m h : ℕ} (p : Projection m h) : 0 < h := p.property.2.2.2
end Projection

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
  induction k generalizing S with
  | zero =>
    rw [Live] at live
    obtain ⟨a, rfl, hg, _⟩ := live
    have gp := p.good a hg
    have nz : p.toFun a≠0 := by intro e;have x := gp 0 p.someRow;simp [e] at x
    exact ⟨0,{p.toFun a},by simp [dead,nz],Live.done gp nz,by simp⟩
  | succ k ih =>
    rw [Live] at live
    obtain ⟨U, a, b, d, rfl, hd, ha, hb, ab, fz, tail⟩ := live
    obtain ⟨j,T,cost,ok,raw⟩ := ih tail
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
def projection (m q r : ℕ) (hr : r < m) : Projection m m := by
  refine ⟨slice m q r, ?_, slice_hom m q r, ?_, by omega⟩
  · simp [slice, half]
  · intro a ga i hi
    rw [slice_lo _ _ _ hi, slice_hi _ _ _ hi]
    cases q.testBit i
    · exact ga r hr
    · exact ga i hi

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
  have has (x : ℕ) (hx : x∈T) : x∈xs := by simpa [xs, p, projection, Projection.toFun, ←rep] using sub x hx
  have test := start_complete live xs has (fuel-xs.count 0) (by omega)
  change (decide (xs.count 0≤fuel) && start m (fuel-xs.count 0) xs)=true
  simp [test,show xs.count 0≤fuel by omega]

def actL : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: ps, w => Nat.bit (w.testBit p) (actL ps w)

theorem actL_testBit : ∀ (pi : List ℕ) (w k : ℕ),
    (actL pi w).testBit k = (pi[k]?.map w.testBit).getD false
  | [], w, k => by simp [actL]
  | p :: ps, w, 0 => by simp [actL, Nat.testBit_bit_zero]
  | p :: ps, w, k + 1 => by simp [actL, Nat.testBit_bit_succ, actL_testBit ps w k]

theorem actL_and (pi : List ℕ) (a b : ℕ) : actL pi (a &&& b) = actL pi a &&& actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_and, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_and]

theorem actL_or (pi : List ℕ) (a b : ℕ) : actL pi (a ||| b) = actL pi a ||| actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_or, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_or]

theorem actL_xor (pi : List ℕ) (a b : ℕ) : actL pi (a ^^^ b) = actL pi a ^^^ actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_xor, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_xor]

def coord (m : ℕ) (r : List ℕ) := actL (r ++ r.map (m+·))

theorem coordC (m : ℕ) (r : List ℕ) (d a b : ℕ) (hd : d < 4) :
    coord m r (combine d a b) = combine d (coord m r a) (coord m r b) := by
  interval_cases d <;> simp [combine,coord,actL_and,actL_or,actL_xor]

def pick {m h : ℕ} (r : List ℕ) (len : r.length=h) (small : ∀ i∈r,i<m) (pos : 0<h) : Projection m h := by
  refine ⟨coord m r, ?_, coordC m r, ?_, pos⟩
  · apply Nat.eq_of_testBit_eq
    intro i
    simp only [coord,actL_testBit,Nat.zero_testBit]
    cases (r ++ r.map (m+·))[i]? <;> simp
  · intro a ha i hi
    have ir : i<r.length := by omega
    have b := ha r[i] (small _ (List.getElem_mem ir))
    have H₁ : (r ++ r.map (m+·))[i]? = some r[i] := by simp [List.getElem?_append,ir]
    have H₂ : (r ++ r.map (m+·))[h+i]? = some (m+r[i]) := by
      have ne : ¬h+i<r.length := by omega
      have sub : h+i-r.length=i := by omega
      simp [List.getElem?_append,ne,sub,ir]
    simpa [coord,actL_testBit,H₁,H₂] using b

def Ban (m fuel : ℕ) (v : List ℕ) := ∀ n, n ≤ fuel → ¬Live m n v.toFinset
def Wide (m fuel : ℕ) (v : List ℕ) := ¬Possible m fuel v

theorem viaSearch {m fuel v} (test : start m fuel v=false) : Wide m fuel v := by
  rintro ⟨k,S,le,live,sub⟩
  have := start_complete live v sub fuel le
  simp_all

theorem viaCut {m h f t : ℕ} {v w : List ℕ} (p : Projection m h)
    (bound : Wide h t w) (nd : v.Nodup)
    (mem : ∀ a∈v, p.toFun a=0 ∨ p.toFun a∈w)
    (cost : f≤t+(v.map p.toFun).count 0) : Ban m f v := by
  intro k lim run
  obtain ⟨j,T,c,ok,incl⟩ := projectLive p run
  have fixed : dead p.toFun v.toFinset=(v.map p.toFun).count 0 := by
    dsimp [dead]
    have E : v.toFinset.filter (fun x => p.toFun x=0) = (v.filter (fun x => decide (p.toFun x=0))).toFinset := by ext x;simp
    rw [E,List.toFinset_card_of_nodup (nd.filter _)]
    simp only [List.count_eq_countP,List.countP_map,Function.comp_apply]
    rw [List.countP_eq_length_filter]
    congr 2
  rw [fixed] at c
  apply bound
  refine ⟨j,T,by omega,ok,?_⟩
  intro x hx
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp (incl _ hx)
  exact (mem y (List.mem_toFinset.mp hy)).resolve_left (liveNonzero ok _ hx)

theorem renameLive {m h k S} (p : Projection m h) (q : Projection h m)
    (run : Live m k S) (rec : ∀ x∈S, q.toFun (p.toFun x)=x) : Live h k (S.image p.toFun) := by
  induction k generalizing S with
  | zero =>
    rw [Live] at run
    obtain ⟨a,rfl,good,nz⟩ := run
    simp only [Finset.image_singleton]
    apply Live.done (p.good a good)
    intro e
    have := rec a (Finset.mem_singleton_self a)
    rw [e,q.atZero] at this
    exact nz this.symm
  | succ k ih =>
    rw [Live] at run
    obtain ⟨U,a,b,d,rfl,hd,ha,hb,ab,fr,tail⟩ := run
    let z := combine d a b
    have ra := rec a (Finset.mem_insert_self _ _)
    have rb := rec b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have rz : q.toFun (p.toFun z)=z := by simp only [z,p.combineEq _ _ _ hd,q.combineEq _ _ _ hd,ra,rb]
    have ru (x) (hx : x∈U) := rec x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))
    have nr := ih tail (by intro x hx; rcases Finset.mem_insert.mp hx with rfl|h; exact rz; exact ru _ h)
    have eqz : p.toFun z=combine d (p.toFun a) (p.toFun b) := p.combineEq _ _ _ hd
    simp only [Finset.image_insert] at nr ⊢
    apply Live.step hd
    · intro e;rw [e,q.atZero] at ra;exact ha ra.symm
    · intro e;rw [e,q.atZero] at rb;exact hb rb.symm
    · intro e;rw [e,rb] at ra;exact ab ra.symm
    · rw [←eqz]
      intro bad
      rcases Finset.mem_insert.mp bad with e|bad
      · have hza := congrArg q.toFun e
        rw [rz,ra] at hza
        exact fr (Finset.mem_insert.mpr (Or.inl hza))
      rcases Finset.mem_insert.mp bad with e|bad
      · have hzb := congrArg q.toFun e
        rw [rz,rb] at hzb
        exact fr (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl hzb)))
      obtain ⟨x,hx,e⟩ := Finset.mem_image.mp bad
      have eq := congrArg q.toFun e
      rw [ru x hx,rz] at eq
      exact fr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (eq ▸ hx : z ∈ U)))
    · simpa only [p.combineEq _ _ _ hd] using nr

theorem viaPerm {m h f v w} (p : Projection m h) (q : Projection h m)
    (ban : Ban h f w) (rec : ∀ a∈v, q.toFun (p.toFun a)=a)
    (eq : (v.map p.toFun).toFinset=w.toFinset) : Ban m f v := by
  intro n hn live
  have ok := renameLive p q live (by simpa using rec)
  apply ban n hn
  have E : (v.map p.toFun).toFinset=v.toFinset.image p.toFun := by ext x;simp
  rw [←eq,E];exact ok

def ordered (v : List ℕ) := v.insertionSort (· ≤ ·)
theorem ord_eq (v : List ℕ) : (ordered v).toFinset=v.toFinset := by
  ext x;simp [ordered,List.mem_insertionSort]
def banList (m f : ℕ) (vs : List (List ℕ)) := ∀ v∈vs, Ban m f v
theorem consBan {m f a l} (h : Ban m f a) (t : banList m f l) : banList m f (a::l) := by
  intro v hv;rcases List.mem_cons.mp hv with rfl|e;exact h;exact t _ e
theorem nilBan (m f) : banList m f [] := by simp [banList]

theorem viaBranch {m f : ℕ} {v : List ℕ} {ws : List (List ℕ)} (closed : banList m f ws)
    (nd : v.Nodup) (no : terminal m v=false)
    (test : anyGate m f (fun u => !ws.contains (ordered u)) v=false) : Ban m (f+1) v := by
  intro n lim live
  cases n with
  | zero =>
    rw [Live] at live
    obtain ⟨a,rep,g,_⟩ := live
    have ev := ends g v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self a))
    simp_all
  | succ n =>
    rw [Live] at live
    obtain ⟨U,a,b,d,rep,hd,_,_,ab,fr,tail⟩ := live
    have yes := @transition m f n U a b d v (fun u => !ws.contains (ordered u)) hd ab fr rep nd (by omega) tail (by
      intro u hu nu
      change (!ws.contains (ordered u))=true
      simp
      intro found
      have hv := closed _ found n (by omega)
      rw [ord_eq,hu] at hv
      exact hv tail)
    simp_all

theorem widen {m f v} (ess : ∀ a∈v, ∃ i : Fin m, ∀ b∈v, b.testBit i.val≠b.testBit (m+i.val) → b=a)
    (h : Ban m f v) : Wide m f v := by
  rintro ⟨n,S,le,live,sub⟩
  have eq : S=v.toFinset := by
    apply Finset.Subset.antisymm (fun x hx => List.mem_toFinset.mpr (sub _ hx))
    intro a ha
    obtain ⟨i,hi⟩ := ess a (List.mem_toFinset.mp ha)
    obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
    exact hi b (sub b hb) sep ▸ hb
  exact h n le (eq ▸ live)

theorem viaSmall {m f v} (ex : search m f v=false) (nd : v.Nodup) : Ban m f v := by
  intro n le live
  have := complete m f live le v rfl nd
  simp_all

theorem viaSub {m f v ws} (bs : banList m f ws) (nd : v.Nodup)
    (check : v.sublists.all (fun u => !(u.length≤f+1 && enough m (cover m u)) || ws.contains u)=true) :
    Wide m f v := by
  rintro ⟨n,S,lim,live,sub⟩
  let u := v.filter (fun x => decide (x∈S))
  have eq : u.toFinset=S := by ext x; simp [u]; exact fun hx => sub _ hx
  have nd' : u.Nodup := nd.filter _
  have len := liveSize live
  rw [←eq,List.toFinset_card_of_nodup nd'] at len
  have ok := List.all_eq_true.mp check u (List.mem_sublists.mpr List.filter_sublist)
  have cap : u.length≤f+1 := by omega
  have cov := enoughLive live u eq
  simp [cap,cov] at ok
  exact bs u ok n lim (eq ▸ live)


theorem viaDirect {m f v} (nd : v.Nodup) (test : search m f v = false) : Ban m f v := by
  intro k le run
  have yes := complete m f run le v rfl nd
  simp_all

def graph (x : Fin 7 → Bool) := decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i + 1) 0) false = true)

def posBits : ℕ := 0x44e1c3870e1c3870e1c3870e1c3468d1a3468d1a3468d1a3468c58b162c58b162c58b162c58b0e1c3870e1c3870e1c3870e1b162c58b162c58b162c58b162952a54a952a54a952a54a952a3468d1a3468d1a3468d1a34654a952a54a952a54a952a54a93264c993264c993264c99326448912244891224489122448870e1c3870e1c3870e1c3870e142850a142850a142850a14270e1c3870e1c3870e1c3870e183060c183060c183060c183054a952a54a952a54a952a54a94a952a54a952a54a952a54a9468d1a3468d1a3468d1a3468d12244891224489122448912242850a142850a142850a14284d1a3468d1a3468d1a3468d1a3264c993264c993264c993264993264c993264c993264c9932448912244891224489122448891224489122448912244891162c58b162c58b162c58b162c489122448912244891224489
def negBits : ℕ := 0x40c1420c05080c1014201820203050830142030405080608080c1420c05080c1014201820203050830142030405080608080c1420c05080c1014201820203050830142030405080608080c1420c05080c1014201820203050830142030405080608080c1420c05080c1014201820203050830142030405080608080c1420c05080c1014201820203050830142030405080608080c1420c05080c1014201820203050830142030405080608080c1420c05080c1014201820203050830142030405080608080c1420c05080c1014201820203050830142030405080608080c1420c05080c1014201820203050830142030405080608080c1420c05080c1014201820203050830142030405080608080c1420c05080c1014201820203050830142030405080608080c1420c05080c1014201820203050830142030405080608080
def sample (bank : ℕ) (i : Fin 365) (j : Fin 7) := bank.testBit (7*i.val+j.val)
def inputs : List ℕ := [0x405101440510144051014405101440510144051014405101440510144051014405101440510144051014405101400000000003fff0000000fffc000fffc000fffc00000000000003ffffffc000fffc000fffffff0003ffffffffff,0x1600580160058016005801600580160058016005801600580160058016005801600580160058016005801600580000000fffc0000003fff0003fff0000000fffffff0000000fffc000fffffff0003fff0003ffffffc000fffc000,0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x15805601580560158056015805601580560158056015805601580560158056015805601580560158056015805600003fff0000000fffc0000003ffffffffff0000000fffc000fffffff00000000003ffffffc0000000000fffffff,0x8602180860218086021808602180860218086021808602180860218086021808602180860218086021808602180fffc0000000000ffffffffffc00000000000000000fffffff000000000000000003fffffffffffffffff0000000,0x11804601180460118046011804601180460118046011804601180460118046011804601180460118046011804600ffffffffffffff0000000000000000000000000000ffffffffffffffffffffffffc000000000000000000000000,0x3e007801e007801e007801e007801e007801e007801e007801e007801e007801e007801e007801e007801e007801ffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000]
def seeds : List Wire := inputs.map (fun a => (false,a))
theorem listed : ∀ i : Fin 365, seeds.map (read i.val)=List.ofFn (sample posBits i) ∧
    seeds.map (read (365+i.val))=List.ofFn (sample negBits i) := by decide +kernel
theorem labels : ∀ i : Fin 365, graph (sample posBits i)=true ∧ graph (sample negBits i)=false := by decide +kernel
theorem essential : ∀ a∈inputs, ∃ i : Fin 365, ∀ b∈inputs, b.testBit i.val≠b.testBit (365+i.val) → b=a := by decide +kernel
theorem initial {k S} (live : Live 365 k S) (sub : ∀ a∈S,a∈inputs) : S=inputs.toFinset := by
  apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
  intro a ha
  obtain ⟨i,h⟩ := essential a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
  exact h b (sub b hb) sep ▸ hb
theorem trace (C : Circuit) (fan : FanInTwo C) (eq : circuitFun 7 C=graph) :
    ∃ k≤C.gates.countP counted, Live 365 k inputs.toFinset := by
  let final := execute C.gates seeds
  let out := final.getD C.output zero
  have ev (i : ℕ) : read i out = C.eval (seeds.map (read i)) := by
    rw [show read i out = (final.map (read i)).getD C.output false from (read_get i final C.output).symm]
    rw [show final=execute C.gates seeds from rfl,execute_read i _ _ fan];rfl
  have result (x : Fin 7 → Bool) : C.eval (List.ofFn x)=graph x := congrFun eq x
  have good : Good 365 out.2 := by
    intro i hi same
    let j : Fin 365 := ⟨i,hi⟩
    have diff : read i out=read (365+i) out := by simp [read,same]
    have p := ev i;have n := ev (365+i)
    rw [(listed j).1,result,(labels j).1] at p
    rw [(listed j).2,result,(labels j).2] at n
    rw [p,n] at diff;contradiction
  have nz : out.2≠0 := by
    intro z;have bad := good 0 (by decide);simp [z] at bad
  have found : out.2∈ reps final := (get_simple final C.output).resolve_left nz
  obtain ⟨k,S,limit,live,sub⟩ := extract good nz C.gates seeds found
  have stays : ∀ a∈S, a∈inputs := by simpa [reps,seeds,List.map_map,Function.comp_def] using sub
  exact ⟨k,limit,initial live stays ▸ live⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj0 : Projection 364 50 := pick [44,47,48,49,51,54,55,89,91,114,117,119,120,121,124,125,159,163,173,174,175,176,177,180,181,189,191,198,201,203,205,206,208,209,228,229,231,233,234,236,237,257,292,301,306,335,345,349,362,363] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj1 : Projection 364 50 := pick [1,4,7,9,11,12,13,29,34,35,37,39,40,41,77,99,105,106,107,109,110,111,149,174,175,176,177,179,180,181,189,191,228,231,233,234,235,236,237,249,277,278,301,306,319,321,345,349,362,363] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj2 : Projection 364 48 := pick [29,31,34,39,40,41,44,45,48,53,54,55,59,99,101,106,109,110,111,114,115,120,123,124,125,129,171,174,176,179,180,181,198,199,206,207,208,209,213,221,277,278,292,319,321,335,362,363] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj3 : Projection 364 50 := pick [1,3,4,5,9,11,13,17,19,99,101,103,106,107,109,111,114,115,117,120,121,123,125,129,149,159,163,198,199,201,205,206,207,209,213,221,227,228,229,233,234,235,237,249,257,319,321,335,345,349] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj4 : Projection 364 50 := pick [1,3,4,5,7,11,12,17,19,29,31,33,34,35,39,40,44,45,47,48,49,53,54,59,77,89,91,198,199,201,203,206,207,208,213,221,227,228,229,231,234,235,236,249,257,277,278,292,301,306] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj5 : Projection 364 48 := pick [1,3,4,5,7,9,17,19,29,31,33,34,35,37,44,45,47,48,49,51,59,77,89,91,99,101,103,105,106,107,114,115,117,119,120,121,129,149,159,163,171,173,174,175,176,177,189,191] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj6 : Projection 50 50 := pick [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj7 : Projection 50 50 := pick [0,1,3,2,4,6,5,15,17,18,16,19,21,20,22,7,10,8,9,11,13,12,14,25,26,23,24,27,29,28,31,30,32,34,33,35,36,38,37,39,44,45,46,47,40,41,42,43,49,48] rfl (by decide +kernel) (by decide)
def valeur0 : ℕ := 0x4640202222443380007fffff
def valeur1 : ℕ := 0x1101f15151838ccffc040407f
def valeur2 : ℕ := 0x4388946454c930f80ffc07fff
def valeur3 : ℕ := 0xb811299989123f000ffff8000
def valeur4 : ℕ := 0xeefe0e0e0e1c3ffff00000000
def etat0 : List ℕ := [valeur0,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne8 : Ban 50 4 etat0 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur5 : ℕ := 0x4388946454c930f00ff803f80
def etat1 : List ℕ := [valeur0,valeur1,valeur5,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne9 : Ban 50 4 etat1 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur6 : ℕ := 0x4388946454c930f00ff807f80
def valeur7 : ℕ := 0xb811299989123f080ffffc07f
def etat2 : List ℕ := [valeur0,valeur1,valeur6,valeur7,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne10 : Ban 50 4 etat2 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur8 : ℕ := 0xb811299989123f000ffbf8000
def etat3 : List ℕ := [valeur0,valeur1,valeur6,valeur8,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne11 : Ban 50 4 etat3 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur9 : ℕ := 0xeefe0e0e0e1c3ffff0040407f
def etat4 : List ℕ := [valeur0,valeur1,valeur6,valeur3,valeur9]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne12 : Ban 50 4 etat4 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur10 : ℕ := 0xeefe0e0e0e1c3ff7f00000000
def etat5 : List ℕ := [valeur0,valeur1,valeur6,valeur3,valeur10]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne13 : Ban 50 4 etat5 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur11 : ℕ := 0x800040407f
def valeur12 : ℕ := 0xccff00000000
def etat6 : List ℕ := [valeur11,valeur12,valeur0,valeur6,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne14 : Ban 50 4 etat6 := viaDirect (by decide +kernel) (by decide +kernel)
def etat7 : List ℕ := [valeur11,valeur0,valeur1,valeur6,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne15 : Ban 50 5 etat7 := viaBranch (ws := [etat0,etat1,etat2,etat3,etat4,etat5,etat6]) (consBan borne8 (consBan borne9 (consBan borne10 (consBan borne11 (consBan borne12 (consBan borne13 (consBan borne14 (nilBan 50 4)))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur13 : ℕ := 0x1565f35373a7cffffc07fffff
def etat8 : List ℕ := [valeur0,valeur1,valeur13,valeur6,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne16 : Ban 50 5 etat8 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur14 : ℕ := 0x4640202222443300003fbf80
def etat9 : List ℕ := [valeur14,valeur0,valeur1,valeur6,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne17 : Ban 50 5 etat9 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur15 : ℕ := 0x1101f15151838cc7fc0000000
def etat10 : List ℕ := [valeur0,valeur15,valeur1,valeur6,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne18 : Ban 50 5 etat10 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur16 : ℕ := 0x30000007f80
def etat11 : List ℕ := [valeur16,valeur0,valeur1,valeur6,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne19 : Ban 50 5 etat11 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur17 : ℕ := 0x47ec966676ed73f80ffffffff
def etat12 : List ℕ := [valeur0,valeur1,valeur6,valeur17,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne20 : Ban 50 5 etat12 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur18 : ℕ := 0x4640202222443080007f807f
def etat13 : List ℕ := [valeur18,valeur0,valeur1,valeur6,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne21 : Ban 50 5 etat13 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur19 : ℕ := 0x4388946454c930c00ff800000
def etat14 : List ℕ := [valeur0,valeur1,valeur19,valeur6,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne22 : Ban 50 5 etat14 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur20 : ℕ := 0x3000007f8000
def etat15 : List ℕ := [valeur20,valeur0,valeur1,valeur6,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne23 : Ban 50 5 etat15 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur21 : ℕ := 0xbc752b9bab367f380ffffffff
def etat16 : List ℕ := [valeur0,valeur1,valeur6,valeur3,valeur21,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne24 : Ban 50 5 etat16 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur22 : ℕ := 0x464020222244038000007fff
def etat17 : List ℕ := [valeur22,valeur0,valeur1,valeur6,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne25 : Ban 50 5 etat17 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur23 : ℕ := 0xb811299989123c000ff800000
def etat18 : List ℕ := [valeur0,valeur1,valeur6,valeur23,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne26 : Ban 50 5 etat18 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur24 : ℕ := 0x464020202040338000000000
def etat19 : List ℕ := [valeur24,valeur0,valeur1,valeur6,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne27 : Ban 50 5 etat19 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur25 : ℕ := 0xeefe0e0e2e3c7ffff007fffff
def etat20 : List ℕ := [valeur1,valeur13,valeur6,valeur3,valeur25]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne28 : Ban 50 4 etat20 := viaDirect (by decide +kernel) (by decide +kernel)
def etat21 : List ℕ := [valeur14,valeur1,valeur6,valeur3,valeur25]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne29 : Ban 50 4 etat21 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur26 : ℕ := 0xea9a0c0c0c183cc7f00000000
def etat22 : List ℕ := [valeur0,valeur1,valeur6,valeur3,valeur26]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne30 : Ban 50 4 etat22 := viaDirect (by decide +kernel) (by decide +kernel)
def etat23 : List ℕ := [valeur1,valeur6,valeur3,valeur26,valeur25]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne31 : Ban 50 4 etat23 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur27 : ℕ := 0xccff0040407f
def etat24 : List ℕ := [valeur27,valeur0,valeur6,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne32 : Ban 50 4 etat24 := viaDirect (by decide +kernel) (by decide +kernel)
def etat25 : List ℕ := [valeur27,valeur0,valeur1,valeur6,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne33 : Ban 50 4 etat25 := viaDirect (by decide +kernel) (by decide +kernel)
def etat26 : List ℕ := [valeur27,valeur0,valeur6,valeur3,valeur25]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne34 : Ban 50 4 etat26 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur28 : ℕ := 0x1101f151518380000c0000000
def etat27 : List ℕ := [valeur0,valeur28,valeur1,valeur6,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne35 : Ban 50 4 etat27 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur29 : ℕ := 0xeefe0e0e2e3c73300003fbf80
def etat28 : List ℕ := [valeur0,valeur6,valeur3,valeur29,valeur25]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne36 : Ban 50 4 etat28 := viaDirect (by decide +kernel) (by decide +kernel)
def etat29 : List ℕ := [valeur0,valeur1,valeur6,valeur3,valeur25]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne37 : Ban 50 5 etat29 := viaBranch (ws := [etat20,etat21,etat22,etat23,etat24,etat25,etat26,etat27,etat28]) (consBan borne28 (consBan borne29 (consBan borne30 (consBan borne31 (consBan borne32 (consBan borne33 (consBan borne34 (consBan borne35 (consBan borne36 (nilBan 50 4)))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat30 : List ℕ := [valeur0,valeur1,valeur6,valeur3,valeur4,valeur25]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne38 : Ban 50 5 etat30 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur30 : ℕ := 0x202040000007fffff
def etat31 : List ℕ := [valeur30,valeur0,valeur1,valeur6,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne39 : Ban 50 5 etat31 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne40 : Ban 50 5 etat22 := viaDirect (by decide +kernel) (by decide +kernel)
def etat32 : List ℕ := [valeur0,valeur1,valeur6,valeur3,valeur26,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne41 : Ban 50 5 etat32 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur31 : ℕ := 0x1009040508100c00c0004000
def etat33 : List ℕ := [valeur31,valeur0,valeur1,valeur6,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne42 : Ban 50 5 etat33 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur32 : ℕ := 0x5389f57555cbbcfffffc07fff
def etat34 : List ℕ := [valeur0,valeur1,valeur6,valeur32,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne43 : Ban 50 5 etat34 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur33 : ℕ := 0x1001611101028c0ff0040007f
def etat35 : List ℕ := [valeur0,valeur33,valeur1,valeur6,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne44 : Ban 50 5 etat35 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur34 : ℕ := 0x428804240448303003f803f80
def etat36 : List ℕ := [valeur0,valeur1,valeur34,valeur6,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne45 : Ban 50 5 etat36 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur35 : ℕ := 0x1001211101020c000c0400000
def etat37 : List ℕ := [valeur0,valeur35,valeur1,valeur6,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne46 : Ban 50 5 etat37 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur36 : ℕ := 0xb911f9d9d993bfcffffffc07f
def etat38 : List ℕ := [valeur0,valeur1,valeur6,valeur3,valeur36,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne47 : Ban 50 5 etat38 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur37 : ℕ := 0x100d040508180cff0000407f
def etat39 : List ℕ := [valeur37,valeur0,valeur1,valeur6,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne48 : Ban 50 5 etat39 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur38 : ℕ := 0xa81008888810330003fbf8000
def etat40 : List ℕ := [valeur0,valeur1,valeur6,valeur38,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne49 : Ban 50 5 etat40 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur39 : ℕ := 0x464020222244ffff007fffff
def etat41 : List ℕ := [valeur39,valeur1,valeur6,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne50 : Ban 50 4 etat41 := viaDirect (by decide +kernel) (by decide +kernel)
def etat42 : List ℕ := [valeur12,valeur39,valeur1,valeur6,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne51 : Ban 50 4 etat42 := viaDirect (by decide +kernel) (by decide +kernel)
def etat43 : List ℕ := [valeur0,valeur39,valeur1,valeur6,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne52 : Ban 50 4 etat43 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur40 : ℕ := 0xcc7f00000000
def etat44 : List ℕ := [valeur40,valeur0,valeur1,valeur6,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne53 : Ban 50 4 etat44 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur41 : ℕ := 0x4640202222443300007fffff
def etat45 : List ℕ := [valeur12,valeur41,valeur1,valeur6,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne54 : Ban 50 4 etat45 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur42 : ℕ := 0x1101f151518380000c040407f
def etat46 : List ℕ := [valeur12,valeur0,valeur42,valeur6,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne55 : Ban 50 4 etat46 := viaDirect (by decide +kernel) (by decide +kernel)
def etat47 : List ℕ := [valeur0,valeur42,valeur1,valeur6,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne56 : Ban 50 4 etat47 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur43 : ℕ := 0x4388946454c93cfffff807f80
def etat48 : List ℕ := [valeur12,valeur0,valeur1,valeur43,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne57 : Ban 50 4 etat48 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur44 : ℕ := 0x4388946454c930300ff807f80
def etat49 : List ℕ := [valeur12,valeur0,valeur1,valeur44,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne58 : Ban 50 4 etat49 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur45 : ℕ := 0xb811299989123fcffffff8000
def etat50 : List ℕ := [valeur12,valeur0,valeur1,valeur6,valeur45]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne59 : Ban 50 4 etat50 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur46 : ℕ := 0xb8112999891233000ffff8000
def etat51 : List ℕ := [valeur12,valeur0,valeur1,valeur6,valeur46]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne60 : Ban 50 4 etat51 := viaDirect (by decide +kernel) (by decide +kernel)
def etat52 : List ℕ := [valeur12,valeur14,valeur0,valeur6,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne61 : Ban 50 4 etat52 := viaDirect (by decide +kernel) (by decide +kernel)
def etat53 : List ℕ := [valeur12,valeur0,valeur6,valeur32,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne62 : Ban 50 4 etat53 := viaDirect (by decide +kernel) (by decide +kernel)
def etat54 : List ℕ := [valeur12,valeur0,valeur33,valeur6,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne63 : Ban 50 4 etat54 := viaDirect (by decide +kernel) (by decide +kernel)
def etat55 : List ℕ := [valeur12,valeur0,valeur6,valeur3,valeur36]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne64 : Ban 50 4 etat55 := viaDirect (by decide +kernel) (by decide +kernel)
def etat56 : List ℕ := [valeur12,valeur37,valeur0,valeur6,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne65 : Ban 50 4 etat56 := viaDirect (by decide +kernel) (by decide +kernel)
def etat57 : List ℕ := [valeur12,valeur0,valeur1,valeur6,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne66 : Ban 50 5 etat57 := viaBranch (ws := [etat41,etat42,etat43,etat44,etat45,etat46,etat47,etat48,etat49,etat50,etat51,etat6,etat52,etat53,etat54,etat55,etat56]) (consBan borne50 (consBan borne51 (consBan borne52 (consBan borne53 (consBan borne54 (consBan borne55 (consBan borne56 (consBan borne57 (consBan borne58 (consBan borne59 (consBan borne60 (consBan borne14 (consBan borne61 (consBan borne62 (consBan borne63 (consBan borne64 (consBan borne65 (nilBan 50 4)))))))))))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat58 : List ℕ := [valeur12,valeur0,valeur1,valeur6,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne67 : Ban 50 5 etat58 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur47 : ℕ := 0xffffff5f5f9fbffffc040407f
def etat59 : List ℕ := [valeur0,valeur1,valeur6,valeur3,valeur4,valeur47]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne68 : Ban 50 5 etat59 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne69 : Ban 50 5 etat47 := viaDirect (by decide +kernel) (by decide +kernel)
def etat60 : List ℕ := [valeur0,valeur42,valeur1,valeur6,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne70 : Ban 50 5 etat60 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur48 : ℕ := 0xeefe0e0e0e1c3330000000000
def etat61 : List ℕ := [valeur0,valeur1,valeur6,valeur3,valeur48,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne71 : Ban 50 5 etat61 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur49 : ℕ := 0x4640202222473380ffffffff
def etat62 : List ℕ := [valeur49,valeur1,valeur6,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne72 : Ban 50 4 etat62 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur50 : ℕ := 0x1101f1515183bccffffc0407f
def etat63 : List ℕ := [valeur0,valeur50,valeur6,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne73 : Ban 50 4 etat63 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur51 : ℕ := 0x1101f15151838ccff0040407f
def etat64 : List ℕ := [valeur0,valeur51,valeur6,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne74 : Ban 50 4 etat64 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur52 : ℕ := 0xeefe0e0e0e1c3ffffff800000
def etat65 : List ℕ := [valeur0,valeur1,valeur6,valeur3,valeur52]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne75 : Ban 50 4 etat65 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur53 : ℕ := 0xeefe0e0e0e1c0ffff00000000
def etat66 : List ℕ := [valeur0,valeur1,valeur6,valeur3,valeur53]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne76 : Ban 50 4 etat66 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur54 : ℕ := 0x30000ff800000
def valeur55 : ℕ := 0xfb99bdfddddb3ff00ffffff80
def etat67 : List ℕ := [valeur54,valeur0,valeur1,valeur4,valeur55]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne77 : Ban 50 4 etat67 := viaDirect (by decide +kernel) (by decide +kernel)
def etat68 : List ℕ := [valeur54,valeur0,valeur1,valeur6,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne78 : Ban 50 5 etat68 := viaBranch (ws := [etat62,etat63,etat64,etat65,etat66,etat67]) (consBan borne72 (consBan borne73 (consBan borne74 (consBan borne75 (consBan borne76 (consBan borne77 (nilBan 50 4))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat69 : List ℕ := [valeur0,valeur1,valeur6,valeur3,valeur4,valeur55]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne79 : Ban 50 5 etat69 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur56 : ℕ := 0x4388946454c900f0000007f80
def etat70 : List ℕ := [valeur0,valeur1,valeur56,valeur6,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne80 : Ban 50 5 etat70 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur57 : ℕ := 0xb811299989120f000007f8000
def etat71 : List ℕ := [valeur0,valeur1,valeur6,valeur57,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne81 : Ban 50 5 etat71 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur58 : ℕ := 0x42880404040830f0000000000
def etat72 : List ℕ := [valeur0,valeur1,valeur58,valeur6,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne82 : Ban 50 5 etat72 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur59 : ℕ := 0xeffe9e6e5edd3ffffff807f80
def etat73 : List ℕ := [valeur0,valeur1,valeur6,valeur3,valeur4,valeur59]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne83 : Ban 50 5 etat73 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur60 : ℕ := 0x100906050c100000ff807f80
def etat74 : List ℕ := [valeur60,valeur0,valeur1,valeur6,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne84 : Ban 50 5 etat74 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur61 : ℕ := 0xac760a0a0a140f0ff00000000
def etat75 : List ℕ := [valeur0,valeur1,valeur6,valeur61,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne85 : Ban 50 5 etat75 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur62 : ℕ := 0xa810080808103f00000000000
def etat76 : List ℕ := [valeur0,valeur1,valeur6,valeur62,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne86 : Ban 50 5 etat76 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur63 : ℕ := 0xfeff2f9f8f1e3ffffffff8000
def etat77 : List ℕ := [valeur0,valeur1,valeur6,valeur3,valeur4,valeur63]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne87 : Ban 50 5 etat77 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur64 : ℕ := 0x10012191810200000ffff8000
def etat78 : List ℕ := [valeur0,valeur64,valeur1,valeur6,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne88 : Ban 50 5 etat78 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur65 : ℕ := 0x46ee0606060c00fff00000000
def etat79 : List ℕ := [valeur0,valeur1,valeur6,valeur65,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne89 : Ban 50 5 etat79 := viaDirect (by decide +kernel) (by decide +kernel)
def etat80 : List ℕ := [valeur0,valeur1,valeur6,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne90 : Ban 50 6 etat80 := viaBranch (ws := [etat7,etat8,etat9,etat10,etat11,etat12,etat13,etat14,etat15,etat16,etat17,etat18,etat19,etat29,etat30,etat31,etat22,etat32,etat33,etat34,etat35,etat36,etat37,etat38,etat39,etat40,etat57,etat58,etat59,etat47,etat60,etat61,etat68,etat69,etat70,etat71,etat72,etat73,etat74,etat75,etat76,etat77,etat78,etat79]) (consBan borne15 (consBan borne16 (consBan borne17 (consBan borne18 (consBan borne19 (consBan borne20 (consBan borne21 (consBan borne22 (consBan borne23 (consBan borne24 (consBan borne25 (consBan borne26 (consBan borne27 (consBan borne37 (consBan borne38 (consBan borne39 (consBan borne40 (consBan borne41 (consBan borne42 (consBan borne43 (consBan borne44 (consBan borne45 (consBan borne46 (consBan borne47 (consBan borne48 (consBan borne49 (consBan borne66 (consBan borne67 (consBan borne68 (consBan borne69 (consBan borne70 (consBan borne71 (consBan borne78 (consBan borne79 (consBan borne80 (consBan borne81 (consBan borne82 (consBan borne83 (consBan borne84 (consBan borne85 (consBan borne86 (consBan borne87 (consBan borne88 (consBan borne89 (nilBan 50 5))))))))))))))))))))))))))))))))))))))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne91 : Wide 50 6 etat80 := widen (by decide +kernel) borne90
def valeur66 : ℕ := 0x800200080020008002000800200080020008002000800200080020008002000800200080020008002000800200000000000000000000000003fff000000000000000000000fffc00000000000003fff00000000000000fffc000
def valeur67 : ℕ := 0xb002c00b002c00b002c00b002c00b002c00b002c00b002c00b002c00b002c00b002c00b002c00b002c00b002c0000000fffc0000003fff0003fff0000000fffffff0000000fffc000fffffff0003fff0003ffffffc000fffc000
def valeur68 : ℕ := 0xac02b00ac02b00ac02b00ac02b00ac02b00ac02b00ac02b00ac02b00ac02b00ac02b00ac02b00ac02b00ac02b00003fff0000000fffc0000003ffffffffff0000000fffc000fffffff00000000003ffffffc0000000000fffffff
def valeur69 : ℕ := 0x202880a202880a202880a202880a202880a202880a202880a202880a202880a202880a202880a202880a202880a00000000003fff0000000fffc000fffc000fffc00000000000003ffffffc000fffc000fffffff0003ffffffffff
def valeur70 : ℕ := 0x43010c043010c043010c043010c043010c043010c043010c043010c043010c043010c043010c043010c043010c0fffc0000000000ffffffffffc00000000000000000fffffff000000000000000003fffffffffffffffff0000000
def valeur71 : ℕ := 0x8c023008c023008c023008c023008c023008c023008c023008c023008c023008c023008c023008c023008c02300ffffffffffffff0000000000000000000000000000ffffffffffffffffffffffffc000000000000000000000000
def valeur72 : ℕ := 0xf003c00f003c00f003c00f003c00f003c00f003c00f003c00f003c00f003c00f003c00f003c00f003c00f003c00ffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000
def etat81 : List ℕ := [valeur66,valeur67,valeur68,valeur69,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne92 : Ban 364 7 etat81 := viaCut proj1 borne91 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur73 : ℕ := 0xaf02bc0af02bc0af02bc0af02bc0af02bc0af02bc0af02bc0af02bc0af02bc0af02bc0af02bc0af02bc0af02bc0003ffffffc000fffffff0003ffffffffffffffffffffc000ffffffffffffff0003fffffffffffffc000fffffff
def etat82 : List ℕ := [valeur67,valeur68,valeur73,valeur69,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne93 : Ban 364 7 etat82 := viaCut proj1 borne91 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur74 : ℕ := 0x3000c003000c003000c003000c003000c003000c003000c003000c003000c003000c003000c003000c003000c0000000fffc0000003fff00000000000000fffffff00000000000000fffffff00000000003ffffffc0000000000
def etat83 : List ℕ := [valeur74,valeur67,valeur68,valeur69,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne94 : Ban 364 7 etat83 := viaCut proj1 borne91 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur75 : ℕ := 0xa402900a402900a402900a402900a402900a402900a402900a402900a402900a402900a402900a402900a402900003fff0000000fffc0000000000fffffff0000000fffc0000003fff00000000000000fffc00000000000003fff
def etat84 : List ℕ := [valeur67,valeur75,valeur68,valeur69,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne95 : Ban 364 7 etat84 := viaCut proj1 borne91 (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj96 : Projection 50 50 := pick [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj97 : Projection 50 50 := pick [9,10,12,13,11,15,14,16,17,0,1,4,2,3,6,5,7,8,18,21,22,19,20,24,23,26,25,27,28,30,29,31,33,32,34,35,37,36,38,40,39,41,45,46,47,42,43,44,49,48] rfl (by decide +kernel) (by decide)
def valeur76 : ℕ := 0x82040141208020000030180
def valeur77 : ℕ := 0x82060141a0c2603f803ffff
def valeur78 : ℕ := 0x128f1d95cb668dbfc06030180
def valeur79 : ℕ := 0x472448a6124b31c0007fc01ff
def valeur80 : ℕ := 0xb8489158ac143e00007fffe00
def valeur81 : ℕ := 0xed70e06030183fffff8000000
def etat85 : List ℕ := [valeur76,valeur77,valeur78,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne98 : Ban 50 5 etat85 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur82 : ℕ := 0x120d19948a460d9fc06000000
def etat86 : List ℕ := [valeur77,valeur82,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne99 : Ban 50 4 etat86 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur83 : ℕ := 0x128f1f95cbe6cfffffe03ffff
def etat87 : List ℕ := [valeur82,valeur83,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne100 : Ban 50 4 etat87 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur84 : ℕ := 0xedf2e66171b8ffffff803ffff
def etat88 : List ℕ := [valeur83,valeur79,valeur80,valeur81,valeur84]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne101 : Ban 50 4 etat88 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur85 : ℕ := 0x82060141a0c00000003ffff
def etat89 : List ℕ := [valeur85,valeur83,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne102 : Ban 50 4 etat89 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur86 : ℕ := 0xfffff8000000
def etat90 : List ℕ := [valeur86,valeur77,valeur79,valeur80]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne103 : Ban 50 4 etat90 := viaDirect (by decide +kernel) (by decide +kernel)
def etat91 : List ℕ := [valeur86,valeur77,valeur83,valeur79,valeur80]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne104 : Ban 50 4 etat91 := viaDirect (by decide +kernel) (by decide +kernel)
def etat92 : List ℕ := [valeur86,valeur77,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne105 : Ban 50 4 etat92 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur87 : ℕ := 0x128f1f95cbe6c00000603ffff
def etat93 : List ℕ := [valeur77,valeur87,valeur83,valeur79,valeur80]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne106 : Ban 50 4 etat93 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur88 : ℕ := 0xed70e06030183000000000000
def etat94 : List ℕ := [valeur77,valeur79,valeur80,valeur88,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne107 : Ban 50 4 etat94 := viaDirect (by decide +kernel) (by decide +kernel)
def etat95 : List ℕ := [valeur77,valeur83,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne108 : Ban 50 5 etat95 := viaBranch (ws := [etat86,etat87,etat88,etat89,etat90,etat91,etat92,etat93,etat94]) (consBan borne99 (consBan borne100 (consBan borne101 (consBan borne102 (consBan borne103 (consBan borne104 (consBan borne105 (consBan borne106 (consBan borne107 (nilBan 50 4)))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat96 : List ℕ := [valeur77,valeur78,valeur83,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne109 : Ban 50 5 etat96 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur89 : ℕ := 0x200008042403f800fe7f
def etat97 : List ℕ := [valeur89,valeur77,valeur78,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne110 : Ban 50 5 etat97 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne111 : Ban 50 5 etat86 := viaDirect (by decide +kernel) (by decide +kernel)
def etat98 : List ℕ := [valeur77,valeur82,valeur78,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne112 : Ban 50 5 etat98 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur90 : ℕ := 0x400000001ff
def etat99 : List ℕ := [valeur90,valeur77,valeur78,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne113 : Ban 50 5 etat99 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur91 : ℕ := 0x47a64ea753ebf3e03ffffffff
def etat100 : List ℕ := [valeur77,valeur78,valeur79,valeur91,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne114 : Ban 50 5 etat100 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur92 : ℕ := 0x82060141a0c2203f803fe00
def etat101 : List ℕ := [valeur92,valeur77,valeur78,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne115 : Ban 50 5 etat101 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur93 : ℕ := 0x472448a6124b3180007fc0000
def etat102 : List ℕ := [valeur77,valeur78,valeur93,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne116 : Ban 50 5 etat102 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur94 : ℕ := 0x20000003fe00
def etat103 : List ℕ := [valeur94,valeur77,valeur78,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne117 : Ban 50 5 etat103 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur95 : ℕ := 0xb8ca9759edb4fe603ffffffff
def etat104 : List ℕ := [valeur77,valeur78,valeur79,valeur80,valeur95,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne118 : Ban 50 5 etat104 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur96 : ℕ := 0x82060141a0c0603f80001ff
def etat105 : List ℕ := [valeur96,valeur77,valeur78,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne119 : Ban 50 5 etat105 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur97 : ℕ := 0xb8489158ac143c00007fc0000
def etat106 : List ℕ := [valeur77,valeur78,valeur79,valeur97,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne120 : Ban 50 5 etat106 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur98 : ℕ := 0x128f1d95cb668fffffe030180
def etat107 : List ℕ := [valeur77,valeur98,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne121 : Ban 50 4 etat107 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur99 : ℕ := 0x128f1d95cb668d9fc06030180
def etat108 : List ℕ := [valeur77,valeur99,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne122 : Ban 50 4 etat108 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur100 : ℕ := 0x472448a6124b33e03fffc01ff
def etat109 : List ℕ := [valeur77,valeur78,valeur100,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne123 : Ban 50 4 etat109 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur101 : ℕ := 0x472448a6124b3180007fc01ff
def etat110 : List ℕ := [valeur77,valeur78,valeur101,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne124 : Ban 50 4 etat110 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur102 : ℕ := 0xb8489158ac143e603fffffe00
def etat111 : List ℕ := [valeur77,valeur78,valeur79,valeur102,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne125 : Ban 50 4 etat111 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur103 : ℕ := 0xb8489158ac143c00007fffe00
def etat112 : List ℕ := [valeur77,valeur78,valeur79,valeur103,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne126 : Ban 50 4 etat112 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur104 : ℕ := 0x2603f8000000
def valeur105 : ℕ := 0xdbfc00000000
def etat113 : List ℕ := [valeur104,valeur105,valeur77,valeur79,valeur80]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne127 : Ban 50 4 etat113 := viaDirect (by decide +kernel) (by decide +kernel)
def etat114 : List ℕ := [valeur104,valeur77,valeur78,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne128 : Ban 50 5 etat114 := viaBranch (ws := [etat107,etat108,etat109,etat110,etat111,etat112,etat113]) (consBan borne121 (consBan borne122 (consBan borne123 (consBan borne124 (consBan borne125 (consBan borne126 (consBan borne127 (nilBan 50 4)))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat115 : List ℕ := [valeur77,valeur78,valeur79,valeur80,valeur81,valeur84]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne129 : Ban 50 5 etat115 := viaDirect (by decide +kernel) (by decide +kernel)
def etat116 : List ℕ := [valeur85,valeur77,valeur78,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne130 : Ban 50 5 etat116 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur106 : ℕ := 0xed70e06030183d9fc00000000
def etat117 : List ℕ := [valeur77,valeur78,valeur79,valeur80,valeur106,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne131 : Ban 50 5 etat117 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur107 : ℕ := 0x204088402420180006000180
def etat118 : List ℕ := [valeur77,valeur107,valeur78,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne132 : Ban 50 5 etat118 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur108 : ℕ := 0x57af5db7db6fbdffc07ff01ff
def etat119 : List ℕ := [valeur77,valeur78,valeur79,valeur108,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne133 : Ban 50 5 etat119 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur109 : ℕ := 0x108b1511c9248c3fc00030000
def etat120 : List ℕ := [valeur77,valeur109,valeur78,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne134 : Ban 50 5 etat120 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur110 : ℕ := 0x4520402210093040001fc007f
def etat121 : List ℕ := [valeur77,valeur78,valeur110,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne135 : Ban 50 5 etat121 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur111 : ℕ := 0x1008111088040c00006030000
def etat122 : List ℕ := [valeur77,valeur111,valeur78,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne136 : Ban 50 5 etat122 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur112 : ℕ := 0xbacf9dddef76bfbfc07ffff80
def etat123 : List ℕ := [valeur77,valeur78,valeur79,valeur80,valeur112,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne137 : Ban 50 5 etat123 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur113 : ℕ := 0x2870c85436281bfc00000180
def etat124 : List ℕ := [valeur77,valeur113,valeur78,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne138 : Ban 50 5 etat124 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur114 : ℕ := 0xa840804824103200001fcfe00
def etat125 : List ℕ := [valeur77,valeur78,valeur79,valeur114,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne139 : Ban 50 5 etat125 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur115 : ℕ := 0x82060141a0cfffff803ffff
def etat126 : List ℕ := [valeur115,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne140 : Ban 50 4 etat126 := viaDirect (by decide +kernel) (by decide +kernel)
def etat127 : List ℕ := [valeur105,valeur115,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne141 : Ban 50 4 etat127 := viaDirect (by decide +kernel) (by decide +kernel)
def etat128 : List ℕ := [valeur77,valeur115,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne142 : Ban 50 4 etat128 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur116 : ℕ := 0xd9fc00000000
def etat129 : List ℕ := [valeur116,valeur77,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne143 : Ban 50 4 etat129 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur117 : ℕ := 0x82060141a0c2403f803ffff
def etat130 : List ℕ := [valeur105,valeur117,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne144 : Ban 50 4 etat130 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur118 : ℕ := 0x472448a6124b3dffc07fc01ff
def etat131 : List ℕ := [valeur105,valeur77,valeur118,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne145 : Ban 50 4 etat131 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur119 : ℕ := 0x472448a6124b3040007fc01ff
def etat132 : List ℕ := [valeur105,valeur77,valeur119,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne146 : Ban 50 4 etat132 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur120 : ℕ := 0xb8489158ac143fbfc07fffe00
def etat133 : List ℕ := [valeur105,valeur77,valeur79,valeur120,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne147 : Ban 50 4 etat133 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur121 : ℕ := 0xb8489158ac143200007fffe00
def etat134 : List ℕ := [valeur105,valeur77,valeur79,valeur121,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne148 : Ban 50 4 etat134 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur122 : ℕ := 0xed70e060301832403f8000000
def etat135 : List ℕ := [valeur105,valeur77,valeur79,valeur80,valeur122]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne149 : Ban 50 4 etat135 := viaDirect (by decide +kernel) (by decide +kernel)
def etat136 : List ℕ := [valeur77,valeur79,valeur80,valeur122,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne150 : Ban 50 4 etat136 := viaDirect (by decide +kernel) (by decide +kernel)
def etat137 : List ℕ := [valeur105,valeur85,valeur77,valeur79,valeur80]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne151 : Ban 50 4 etat137 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur123 : ℕ := 0xef74e8e6325b3fffffffc01ff
def etat138 : List ℕ := [valeur105,valeur77,valeur79,valeur80,valeur123]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne152 : Ban 50 4 etat138 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur124 : ℕ := 0xa850a04020100e3fff8000000
def etat139 : List ℕ := [valeur105,valeur77,valeur79,valeur124,valeur80]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne153 : Ban 50 4 etat139 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur125 : ℕ := 0xfd78f178bc1c3fffffffffe00
def etat140 : List ℕ := [valeur105,valeur77,valeur79,valeur80,valeur125]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne154 : Ban 50 4 etat140 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur126 : ℕ := 0x45306020100801ffff8000000
def etat141 : List ℕ := [valeur105,valeur77,valeur126,valeur79,valeur80]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne155 : Ban 50 4 etat141 := viaDirect (by decide +kernel) (by decide +kernel)
def etat142 : List ℕ := [valeur105,valeur77,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne156 : Ban 50 5 etat142 := viaBranch (ws := [etat126,etat127,etat128,etat129,etat130,etat131,etat132,etat133,etat134,etat135,etat136,etat113,etat137,etat138,etat139,etat140,etat141]) (consBan borne140 (consBan borne141 (consBan borne142 (consBan borne143 (consBan borne144 (consBan borne145 (consBan borne146 (consBan borne147 (consBan borne148 (consBan borne149 (consBan borne150 (consBan borne127 (consBan borne151 (consBan borne152 (consBan borne153 (consBan borne154 (consBan borne155 (nilBan 50 4)))))))))))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat143 : List ℕ := [valeur105,valeur77,valeur78,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne157 : Ban 50 5 etat143 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur127 : ℕ := 0xfffffdf5fb7ebfffffe030180
def etat144 : List ℕ := [valeur77,valeur78,valeur79,valeur80,valeur81,valeur127]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne158 : Ban 50 5 etat144 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur128 : ℕ := 0x128f1d95cb668000006030180
def etat145 : List ℕ := [valeur77,valeur128,valeur78,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne159 : Ban 50 5 etat145 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne160 : Ban 50 5 etat136 := viaDirect (by decide +kernel) (by decide +kernel)
def etat146 : List ℕ := [valeur77,valeur78,valeur79,valeur80,valeur122,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne161 : Ban 50 5 etat146 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur129 : ℕ := 0x82060141a0f2603ffffffff
def etat147 : List ℕ := [valeur129,valeur78,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne162 : Ban 50 4 etat147 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur130 : ℕ := 0x128f1d95cb66bdbfc07ff0180
def etat148 : List ℕ := [valeur77,valeur130,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne163 : Ban 50 4 etat148 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur131 : ℕ := 0x128f1d95cb668dbfc00030180
def etat149 : List ℕ := [valeur77,valeur131,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne164 : Ban 50 4 etat149 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur132 : ℕ := 0xed70e06030183fffffffc0000
def etat150 : List ℕ := [valeur77,valeur78,valeur79,valeur80,valeur132]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne165 : Ban 50 4 etat150 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur133 : ℕ := 0xed70e06030180fffff8000000
def etat151 : List ℕ := [valeur77,valeur78,valeur79,valeur80,valeur133]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne166 : Ban 50 4 etat151 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur134 : ℕ := 0x3000007fc0000
def valeur135 : ℕ := 0xff6cd9febe5f3fc0007ffffff
def etat152 : List ℕ := [valeur134,valeur77,valeur78,valeur81,valeur135]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne167 : Ban 50 4 etat152 := viaDirect (by decide +kernel) (by decide +kernel)
def etat153 : List ℕ := [valeur134,valeur77,valeur78,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne168 : Ban 50 5 etat153 := viaBranch (ws := [etat147,etat148,etat149,etat150,etat151,etat152]) (consBan borne162 (consBan borne163 (consBan borne164 (consBan borne165 (consBan borne166 (consBan borne167 (nilBan 50 4))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat154 : List ℕ := [valeur77,valeur78,valeur79,valeur80,valeur81,valeur135]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne169 : Ban 50 5 etat154 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur136 : ℕ := 0x472448a6124b01c00000001ff
def etat155 : List ℕ := [valeur77,valeur78,valeur136,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne170 : Ban 50 5 etat155 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur137 : ℕ := 0xb8489158ac140e0000003fe00
def etat156 : List ℕ := [valeur77,valeur78,valeur79,valeur137,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne171 : Ban 50 5 etat156 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur138 : ℕ := 0x45204020100831c0000000000
def etat157 : List ℕ := [valeur77,valeur78,valeur138,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne172 : Ban 50 5 etat157 := viaDirect (by decide +kernel) (by decide +kernel)
def etat158 : List ℕ := [valeur77,valeur78,valeur79,valeur80,valeur81,valeur123]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne173 : Ban 50 5 etat158 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur139 : ℕ := 0x204088602430000007fc01ff
def etat159 : List ℕ := [valeur77,valeur139,valeur78,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne174 : Ban 50 5 etat159 := viaDirect (by decide +kernel) (by decide +kernel)
def etat160 : List ℕ := [valeur77,valeur78,valeur79,valeur124,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne175 : Ban 50 5 etat160 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur140 : ℕ := 0xa840804020103e00000000000
def etat161 : List ℕ := [valeur77,valeur78,valeur79,valeur140,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne176 : Ban 50 5 etat161 := viaDirect (by decide +kernel) (by decide +kernel)
def etat162 : List ℕ := [valeur77,valeur78,valeur79,valeur80,valeur81,valeur125]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne177 : Ban 50 5 etat162 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur141 : ℕ := 0x100811188c040000007fffe00
def etat163 : List ℕ := [valeur77,valeur141,valeur78,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne178 : Ban 50 5 etat163 := viaDirect (by decide +kernel) (by decide +kernel)
def etat164 : List ℕ := [valeur77,valeur78,valeur126,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne179 : Ban 50 5 etat164 := viaDirect (by decide +kernel) (by decide +kernel)
def etat165 : List ℕ := [valeur77,valeur78,valeur79,valeur80,valeur81]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne180 : Ban 50 6 etat165 := viaBranch (ws := [etat85,etat95,etat96,etat97,etat86,etat98,etat99,etat100,etat101,etat102,etat103,etat104,etat105,etat106,etat114,etat115,etat116,etat117,etat118,etat119,etat120,etat121,etat122,etat123,etat124,etat125,etat142,etat143,etat144,etat145,etat136,etat146,etat153,etat154,etat155,etat156,etat157,etat158,etat159,etat160,etat161,etat162,etat163,etat164]) (consBan borne98 (consBan borne108 (consBan borne109 (consBan borne110 (consBan borne111 (consBan borne112 (consBan borne113 (consBan borne114 (consBan borne115 (consBan borne116 (consBan borne117 (consBan borne118 (consBan borne119 (consBan borne120 (consBan borne128 (consBan borne129 (consBan borne130 (consBan borne131 (consBan borne132 (consBan borne133 (consBan borne134 (consBan borne135 (consBan borne136 (consBan borne137 (consBan borne138 (consBan borne139 (consBan borne156 (consBan borne157 (consBan borne158 (consBan borne159 (consBan borne160 (consBan borne161 (consBan borne168 (consBan borne169 (consBan borne170 (consBan borne171 (consBan borne172 (consBan borne173 (consBan borne174 (consBan borne175 (consBan borne176 (consBan borne177 (consBan borne178 (consBan borne179 (nilBan 50 5))))))))))))))))))))))))))))))))))))))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne181 : Wide 50 6 etat165 := widen (by decide +kernel) borne180
def valeur142 : ℕ := 0x2000800200080020008002000800200080020008002000800200080020008002000800200080020008002000800000000000000000000000000000000000fffc00000000000000000fffc00000000000003fff0000000fffc000
def etat166 : List ℕ := [valeur142,valeur67,valeur68,valeur69,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne182 : Ban 364 7 etat166 := viaCut proj0 borne181 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur143 : ℕ := 0x20b882e20b882e20b882e20b882e20b882e20b882e20b882e20b882e20b882e20b882e20b882e20b882e20b882e0000000fffffff0003fffffffffffffc000fffffff0000000ffffffffffffffffffffffffffffffffffffffffff
def etat167 : List ℕ := [valeur67,valeur68,valeur69,valeur143,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne183 : Ban 364 7 etat167 := viaCut proj0 borne181 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur144 : ℕ := 0x900240090024009002400900240090024009002400900240090024009002400900240090024009002400900240000000fffc0000003fff0003fff00000000003fff0000000fffc0000003fff0003fff0000000fffc0000000000
def etat168 : List ℕ := [valeur144,valeur67,valeur68,valeur69,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne184 : Ban 364 7 etat168 := viaCut proj0 borne181 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur145 : ℕ := 0x200880220088022008802200880220088022008802200880220088022008802200880220088022008802200880200000000003fff0000000fffc000fffc000000000000000000003fff0000000fffc000fffc0000003fff0003fff
def etat169 : List ℕ := [valeur67,valeur68,valeur145,valeur69,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne185 : Ban 364 7 etat169 := viaCut proj0 borne181 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur146 : ℕ := 0x3fff0000000000000000000000000000000000000000000003fff0003ffffffc0000000000
def etat170 : List ℕ := [valeur146,valeur67,valeur68,valeur69,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne186 : Ban 364 7 etat170 := viaCut proj1 borne91 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur147 : ℕ := 0x43b10ec43b10ec43b10ec43b10ec43b10ec43b10ec43b10ec43b10ec43b10ec43b10ec43b10ec43b10ec43b10ecfffc000fffc000ffffffffffffff0000000fffffffffffffffffc000fffffff0003ffffffffffffffffffffc000
def etat171 : List ℕ := [valeur67,valeur68,valeur69,valeur70,valeur147,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne187 : Ban 364 7 etat171 := viaCut proj1 borne91 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur148 : ℕ := 0xb002c00b002c00b002c00b002c00b002c00b002c00b002c00b002c00b002c00b002c00b002c00b002c00b002c0000000fffc00000000000003fff0000000fffffff0000000fffc000fffffff000000000000000000000fffc000
def etat172 : List ℕ := [valeur148,valeur67,valeur68,valeur69,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne188 : Ban 364 7 etat172 := viaCut proj1 borne91 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur149 : ℕ := 0x43010c043010c043010c043010c043010c043010c043010c043010c043010c043010c043010c043010c043010c0fffc0000000000fffc000fffc00000000000000000fffffff000000000000000000000fffc0000003fff0000000
def etat173 : List ℕ := [valeur67,valeur68,valeur69,valeur149,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne189 : Ban 364 7 etat173 := viaCut proj1 borne91 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur150 : ℕ := 0xfffc00000000000000000000000000000000000000fffc000fffffff0000000000000000000000000000
def etat174 : List ℕ := [valeur150,valeur67,valeur68,valeur69,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne190 : Ban 364 7 etat174 := viaCut proj1 borne91 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur151 : ℕ := 0x8cb232c8cb232c8cb232c8cb232c8cb232c8cb232c8cb232c8cb232c8cb232c8cb232c8cb232c8cb232c8cb232cffffffffffffff0003fff0003fff0000000fffffffffffffffffffffffffffffffffff0003ffffffc000fffc000
def etat175 : List ℕ := [valeur67,valeur68,valeur69,valeur70,valeur71,valeur151,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne191 : Ban 364 7 etat175 := viaCut proj1 borne91 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur152 : ℕ := 0xb002c00b002c00b002c00b002c00b002c00b002c00b002c00b002c00b002c00b002c00b002c00b002c00b002c000000000000000003fff0003fff0000000fffffff0000000000000000000000003fff0003ffffffc000fffc000
def etat176 : List ℕ := [valeur152,valeur67,valeur68,valeur69,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne192 : Ban 364 7 etat176 := viaCut proj1 borne91 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur153 : ℕ := 0x8c023008c023008c023008c023008c023008c023008c023008c023008c023008c023008c023008c023008c02300fffffff0003fff0000000000000000000000000000fffffff0003fff0000000fffc000000000000000000000000
def etat177 : List ℕ := [valeur67,valeur68,valeur69,valeur70,valeur153,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne193 : Ban 364 7 etat177 := viaCut proj1 borne91 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur154 : ℕ := 0xfffc0000003fff0003fff0000000fffffff0000000000000000000000000000000000000000000000000
def etat178 : List ℕ := [valeur154,valeur67,valeur68,valeur69,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne194 : Ban 364 7 etat178 := viaCut proj1 borne91 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur155 : ℕ := 0xf0b3c2cf0b3c2cf0b3c2cf0b3c2cf0b3c2cf0b3c2cf0b3c2cf0b3c2cf0b3c2cf0b3c2cf0b3c2cf0b3c2cf0b3c2cffffffffffffffffffffffffffffffffffffffffff0000000fffc000fffffff0003fff0003ffffffc000fffc000
def etat179 : List ℕ := [valeur67,valeur68,valeur69,valeur70,valeur71,valeur72,valeur155]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne195 : Ban 364 7 etat179 := viaCut proj1 borne91 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur156 : ℕ := 0xb002c00b002c00b002c00b002c00b002c00b002c00b002c00b002c00b002c00b002c00b002c00b002c00b002c0000000000000000000000000000000000000000000000000fffc000fffffff0003fff0003ffffffc000fffc000
def etat180 : List ℕ := [valeur156,valeur67,valeur68,valeur69,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne196 : Ban 364 7 etat180 := viaCut proj1 borne91 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur157 : ℕ := 0xf003c00f003c00f003c00f003c00f003c00f003c00f003c00f003c00f003c00f003c00f003c00f003c00f003c00fffffff0003ffffffc000fffc000fffffff00000000000000000000000000000000000000000000000000000000
def etat181 : List ℕ := [valeur67,valeur68,valeur69,valeur70,valeur71,valeur157,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne197 : Ban 364 7 etat181 := viaCut proj1 borne91 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur158 : ℕ := 0xfffc000000000000000000003fff00000000000000fffc0000000000fffffff
def etat182 : List ℕ := [valeur158,valeur67,valeur68,valeur69,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne198 : Ban 364 7 etat182 := viaCut proj0 borne181 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur159 : ℕ := 0x2ae8aba2ae8aba2ae8aba2ae8aba2ae8aba2ae8aba2ae8aba2ae8aba2ae8aba2ae8aba2ae8aba2ae8aba2ae8aba0003fff0003ffffffc000fffffffffffffffffc000fffc000ffffffffffc000ffffffffffffff0003ffffffffff
def etat183 : List ℕ := [valeur67,valeur68,valeur69,valeur159,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne199 : Ban 364 7 etat183 := viaCut proj0 borne181 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur160 : ℕ := 0xac02b00ac02b00ac02b00ac02b00ac02b00ac02b00ac02b00ac02b00ac02b00ac02b00ac02b00ac02b00ac02b00003fff0000000fffc0000003fff0003fff0000000fffc000fffc00000000000003fff000000000000000000000
def etat184 : List ℕ := [valeur67,valeur160,valeur68,valeur69,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne200 : Ban 364 7 etat184 := viaCut proj0 borne181 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur161 : ℕ := 0x202880a202880a202880a202880a202880a202880a202880a202880a202880a202880a202880a202880a202880a00000000003fff0000000fffc0000000000fffc00000000000000000fffc000fffc0000003fff0003fff0000000
def etat185 : List ℕ := [valeur67,valeur68,valeur161,valeur69,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne201 : Ban 364 7 etat185 := viaCut proj0 borne181 (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj202 : Projection 48 48 := pick [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj203 : Projection 48 48 := pick [13,14,15,16,18,17,19,20,21,22,24,23,25,0,1,2,3,5,4,6,7,8,9,11,10,12,26,28,27,29,31,30,32,33,34,35,37,36,38,39,43,44,45,40,41,42,47,46] rfl (by decide +kernel) (by decide)
def valeur162 : ℕ := 0x420610508200c002001000
def valeur163 : ℕ := 0x43061850c224ff03f81fc0
def valeur164 : ℕ := 0x9ca2651728b1bc00207f03f
def valeur165 : ℕ := 0x461048820514c700fc001fff
def valeur166 : ℕ := 0xb02091248820f800ffffe000
def valeur167 : ℕ := 0xffbce1c70e38ffff00000000
def etat186 : List ℕ := [valeur162,valeur163,valeur164,valeur165,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne204 : Ban 48 5 etat186 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur168 : ℕ := 0x988204122091b000007e03f
def etat187 : List ℕ := [valeur163,valeur168,valeur165,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne205 : Ban 48 4 etat187 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur169 : ℕ := 0x9cb265972cb3fff03ffffff
def etat188 : List ℕ := [valeur168,valeur169,valeur165,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne206 : Ban 48 4 etat188 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur170 : ℕ := 0x46534e9a55d6e7fffff81fff
def etat189 : List ℕ := [valeur169,valeur165,valeur170,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne207 : Ban 48 4 etat189 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur171 : ℕ := 0x43061850c220ff03f80000
def etat190 : List ℕ := [valeur171,valeur169,valeur165,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne208 : Ban 48 4 etat190 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur172 : ℕ := 0xb063973cd8e2fcffffffffc0
def etat191 : List ℕ := [valeur169,valeur165,valeur166,valeur172,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne209 : Ban 48 4 etat191 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur173 : ℕ := 0x43061850c204ff00001fc0
def etat192 : List ℕ := [valeur173,valeur169,valeur165,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne210 : Ban 48 4 etat192 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur174 : ℕ := 0x24ff00000000
def valeur175 : ℕ := 0x9cb265972cb1b0003ffffff
def etat193 : List ℕ := [valeur174,valeur175,valeur165,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne211 : Ban 48 3 etat193 := viaDirect (by decide +kernel) (by decide +kernel)
def etat194 : List ℕ := [valeur175,valeur169,valeur165,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne212 : Ban 48 3 etat194 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur176 : ℕ := 0x461048820514e7fffc001fff
def etat195 : List ℕ := [valeur169,valeur176,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne213 : Ban 48 3 etat195 := viaDirect (by decide +kernel) (by decide +kernel)
def etat196 : List ℕ := [valeur174,valeur169,valeur176,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne214 : Ban 48 3 etat196 := viaDirect (by decide +kernel) (by decide +kernel)
def etat197 : List ℕ := [valeur169,valeur165,valeur176,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne215 : Ban 48 3 etat197 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur177 : ℕ := 0x20ff00000000
def etat198 : List ℕ := [valeur177,valeur169,valeur165,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne216 : Ban 48 3 etat198 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur178 : ℕ := 0x461048820514c300fc001fff
def etat199 : List ℕ := [valeur174,valeur169,valeur178,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne217 : Ban 48 3 etat199 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur179 : ℕ := 0xb02091248820fcffffffe000
def etat200 : List ℕ := [valeur169,valeur165,valeur179]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne218 : Ban 48 3 etat200 := viaDirect (by decide +kernel) (by decide +kernel)
def etat201 : List ℕ := [valeur174,valeur169,valeur165,valeur179]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne219 : Ban 48 3 etat201 := viaDirect (by decide +kernel) (by decide +kernel)
def etat202 : List ℕ := [valeur169,valeur165,valeur166,valeur179]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne220 : Ban 48 3 etat202 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur180 : ℕ := 0x4ff00000000
def etat203 : List ℕ := [valeur180,valeur169,valeur165,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne221 : Ban 48 3 etat203 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur181 : ℕ := 0xb02091248820d800ffffe000
def etat204 : List ℕ := [valeur174,valeur169,valeur165,valeur181]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne222 : Ban 48 3 etat204 := viaDirect (by decide +kernel) (by decide +kernel)
def etat205 : List ℕ := [valeur174,valeur169,valeur165,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne223 : Ban 48 4 etat205 := viaBranch (ws := [etat193,etat194,etat195,etat196,etat197,etat198,etat199,etat200,etat201,etat202,etat203,etat204]) (consBan borne211 (consBan borne212 (consBan borne213 (consBan borne214 (consBan borne215 (consBan borne216 (consBan borne217 (consBan borne218 (consBan borne219 (consBan borne220 (consBan borne221 (consBan borne222 (nilBan 48 3))))))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat206 : List ℕ := [valeur174,valeur163,valeur169,valeur165,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne224 : Ban 48 4 etat206 := viaDirect (by decide +kernel) (by decide +kernel)
def etat207 : List ℕ := [valeur174,valeur169,valeur165,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne225 : Ban 48 4 etat207 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur182 : ℕ := 0x43061850c2000003f81fc0
def etat208 : List ℕ := [valeur182,valeur163,valeur169,valeur165,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne226 : Ban 48 4 etat208 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur183 : ℕ := 0xffbce1c70e38db0000000000
def etat209 : List ℕ := [valeur169,valeur165,valeur166,valeur183,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne227 : Ban 48 4 etat209 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur184 : ℕ := 0x988204102083fff00000000
def etat210 : List ℕ := [valeur163,valeur184,valeur169,valeur165,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne228 : Ban 48 4 etat210 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur185 : ℕ := 0x43061870c3000003ffffff
def etat211 : List ℕ := [valeur163,valeur185,valeur169,valeur165,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne229 : Ban 48 4 etat211 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur186 : ℕ := 0xffbce9c70f3cfffffc001fff
def etat212 : List ℕ := [valeur163,valeur169,valeur165,valeur166,valeur186]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne230 : Ban 48 4 etat212 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur187 : ℕ := 0xb9aca1450a2838ff00000000
def etat213 : List ℕ := [valeur163,valeur169,valeur165,valeur166,valeur187]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne231 : Ban 48 4 etat213 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur188 : ℕ := 0xffbcf1e78e38ffffffffe000
def etat214 : List ℕ := [valeur163,valeur169,valeur165,valeur166,valeur188]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne232 : Ban 48 4 etat214 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur189 : ℕ := 0x4f9c60c3061807ff00000000
def etat215 : List ℕ := [valeur163,valeur169,valeur165,valeur189,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne233 : Ban 48 4 etat215 := viaDirect (by decide +kernel) (by decide +kernel)
def etat216 : List ℕ := [valeur163,valeur169,valeur165,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne234 : Ban 48 5 etat216 := viaBranch (ws := [etat187,etat188,etat189,etat190,etat191,etat192,etat205,etat206,etat207,etat208,etat209,etat210,etat211,etat212,etat213,etat214,etat215]) (consBan borne205 (consBan borne206 (consBan borne207 (consBan borne208 (consBan borne209 (consBan borne210 (consBan borne223 (consBan borne224 (consBan borne225 (consBan borne226 (consBan borne227 (consBan borne228 (consBan borne229 (consBan borne230 (consBan borne231 (consBan borne232 (consBan borne233 (nilBan 48 4)))))))))))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat217 : List ℕ := [valeur163,valeur164,valeur169,valeur165,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne235 : Ban 48 5 etat217 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur190 : ℕ := 0x100080040243f01f80fc0
def etat218 : List ℕ := [valeur190,valeur163,valeur164,valeur165,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne236 : Ban 48 5 etat218 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne237 : Ban 48 4 etat216 := viaDirect (by decide +kernel) (by decide +kernel)
def etat219 : List ℕ := [valeur174,valeur163,valeur168,valeur165,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne238 : Ban 48 4 etat219 := viaDirect (by decide +kernel) (by decide +kernel)
def etat220 : List ℕ := [valeur182,valeur163,valeur168,valeur165,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne239 : Ban 48 4 etat220 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur191 : ℕ := 0xffbce1c72e39ffff0007e03f
def etat221 : List ℕ := [valeur163,valeur168,valeur165,valeur166,valeur191]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne240 : Ban 48 4 etat221 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur192 : ℕ := 0xf634c1860c30e4ff00000000
def etat222 : List ℕ := [valeur163,valeur168,valeur165,valeur166,valeur192]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne241 : Ban 48 4 etat222 := viaDirect (by decide +kernel) (by decide +kernel)
def etat223 : List ℕ := [valeur163,valeur168,valeur165,valeur166,valeur186]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne242 : Ban 48 4 etat223 := viaDirect (by decide +kernel) (by decide +kernel)
def etat224 : List ℕ := [valeur163,valeur168,valeur165,valeur166,valeur187]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne243 : Ban 48 4 etat224 := viaDirect (by decide +kernel) (by decide +kernel)
def etat225 : List ℕ := [valeur163,valeur168,valeur165,valeur166,valeur188]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne244 : Ban 48 4 etat225 := viaDirect (by decide +kernel) (by decide +kernel)
def etat226 : List ℕ := [valeur163,valeur168,valeur165,valeur189,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne245 : Ban 48 4 etat226 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne246 : Ban 48 5 etat187 := viaBranch (ws := [etat216,etat188,etat219,etat220,etat221,etat222,etat223,etat224,etat225,etat226]) (consBan borne237 (consBan borne206 (consBan borne238 (consBan borne239 (consBan borne240 (consBan borne241 (consBan borne242 (consBan borne243 (consBan borne244 (consBan borne245 (nilBan 48 4))))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat227 : List ℕ := [valeur163,valeur168,valeur164,valeur165,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne247 : Ban 48 5 etat227 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur193 : ℕ := 0x40000001fc0
def etat228 : List ℕ := [valeur193,valeur163,valeur164,valeur165,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne248 : Ban 48 5 etat228 := viaDirect (by decide +kernel) (by decide +kernel)
def etat229 : List ℕ := [valeur163,valeur164,valeur170,valeur166,valeur186]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne249 : Ban 48 4 etat229 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur194 : ℕ := 0x461040820410e7ff00000000
def etat230 : List ℕ := [valeur163,valeur164,valeur194,valeur165,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne250 : Ban 48 4 etat230 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur195 : ℕ := 0x430e1851c60000fff81fff
def etat231 : List ℕ := [valeur163,valeur195,valeur164,valeur165,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne251 : Ban 48 4 etat231 := viaDirect (by decide +kernel) (by decide +kernel)
def etat232 : List ℕ := [valeur163,valeur164,valeur165,valeur170,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne252 : Ban 48 5 etat232 := viaBranch (ws := [etat189,etat229,etat230,etat231]) (consBan borne207 (consBan borne249 (consBan borne250 (consBan borne251 (nilBan 48 4))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur196 : ℕ := 0x9cb265972cb1fff0207ffff
def etat233 : List ℕ := [valeur163,valeur196,valeur165,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne253 : Ban 48 4 etat233 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur197 : ℕ := 0x988204122091b000207e03f
def etat234 : List ℕ := [valeur163,valeur197,valeur165,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne254 : Ban 48 4 etat234 := viaDirect (by decide +kernel) (by decide +kernel)
def etat235 : List ℕ := [valeur180,valeur163,valeur164,valeur165,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne255 : Ban 48 4 etat235 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur198 : ℕ := 0x43061850c2000000001fc0
def etat236 : List ℕ := [valeur198,valeur163,valeur164,valeur165,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne256 : Ban 48 4 etat236 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur199 : ℕ := 0xb02091248820d800fc07e000
def etat237 : List ℕ := [valeur173,valeur164,valeur165,valeur199,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne257 : Ban 48 4 etat237 := viaDirect (by decide +kernel) (by decide +kernel)
def etat238 : List ℕ := [valeur173,valeur163,valeur164,valeur165,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne258 : Ban 48 5 etat238 := viaBranch (ws := [etat233,etat234,etat235,etat236,etat192,etat237]) (consBan borne253 (consBan borne254 (consBan borne255 (consBan borne256 (consBan borne210 (consBan borne257 (nilBan 48 4))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat239 : List ℕ := [valeur171,valeur163,valeur164,valeur165,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne259 : Ban 48 5 etat239 := viaPerm proj203 proj203 borne258 (by decide +kernel) (by decide +kernel)
def valeur200 : ℕ := 0x461048820514c300fc00003f
def etat240 : List ℕ := [valeur163,valeur164,valeur200,valeur165,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne260 : Ban 48 5 etat240 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur201 : ℕ := 0x200003f80000
def etat241 : List ℕ := [valeur201,valeur163,valeur164,valeur165,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne261 : Ban 48 5 etat241 := viaDirect (by decide +kernel) (by decide +kernel)
def etat242 : List ℕ := [valeur163,valeur164,valeur165,valeur166,valeur172,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne262 : Ban 48 5 etat242 := viaPerm proj203 proj203 borne252 (by decide +kernel) (by decide +kernel)
def etat243 : List ℕ := [valeur163,valeur164,valeur165,valeur199,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne263 : Ban 48 5 etat243 := viaDirect (by decide +kernel) (by decide +kernel)
def etat244 : List ℕ := [valeur174,valeur182,valeur164,valeur165,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne264 : Ban 48 4 etat244 := viaDirect (by decide +kernel) (by decide +kernel)
def etat245 : List ℕ := [valeur182,valeur163,valeur164,valeur165,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne265 : Ban 48 4 etat245 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur202 : ℕ := 0x9ca2651728b3fff0207f03f
def etat246 : List ℕ := [valeur174,valeur163,valeur202,valeur165,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne266 : Ban 48 4 etat246 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur203 : ℕ := 0x9ca2651728b1b000207f03f
def etat247 : List ℕ := [valeur174,valeur163,valeur203,valeur165,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne267 : Ban 48 4 etat247 := viaDirect (by decide +kernel) (by decide +kernel)
def etat248 : List ℕ := [valeur163,valeur164,valeur176,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne268 : Ban 48 4 etat248 := viaDirect (by decide +kernel) (by decide +kernel)
def etat249 : List ℕ := [valeur174,valeur163,valeur164,valeur176,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne269 : Ban 48 4 etat249 := viaDirect (by decide +kernel) (by decide +kernel)
def etat250 : List ℕ := [valeur163,valeur164,valeur165,valeur176,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne270 : Ban 48 4 etat250 := viaDirect (by decide +kernel) (by decide +kernel)
def etat251 : List ℕ := [valeur177,valeur163,valeur164,valeur165,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne271 : Ban 48 4 etat251 := viaDirect (by decide +kernel) (by decide +kernel)
def etat252 : List ℕ := [valeur174,valeur163,valeur164,valeur178,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne272 : Ban 48 4 etat252 := viaDirect (by decide +kernel) (by decide +kernel)
def etat253 : List ℕ := [valeur163,valeur164,valeur165,valeur179]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne273 : Ban 48 4 etat253 := viaDirect (by decide +kernel) (by decide +kernel)
def etat254 : List ℕ := [valeur174,valeur163,valeur164,valeur165,valeur179]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne274 : Ban 48 4 etat254 := viaDirect (by decide +kernel) (by decide +kernel)
def etat255 : List ℕ := [valeur163,valeur164,valeur165,valeur166,valeur179]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne275 : Ban 48 4 etat255 := viaDirect (by decide +kernel) (by decide +kernel)
def etat256 : List ℕ := [valeur174,valeur163,valeur164,valeur165,valeur181]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne276 : Ban 48 4 etat256 := viaDirect (by decide +kernel) (by decide +kernel)
def etat257 : List ℕ := [valeur174,valeur164,valeur169,valeur165,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne277 : Ban 48 4 etat257 := viaDirect (by decide +kernel) (by decide +kernel)
def etat258 : List ℕ := [valeur174,valeur190,valeur164,valeur165,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne278 : Ban 48 4 etat258 := viaDirect (by decide +kernel) (by decide +kernel)
def etat259 : List ℕ := [valeur174,valeur163,valeur164,valeur165,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne279 : Ban 48 5 etat259 := viaBranch (ws := [etat244,etat245,etat246,etat247,etat248,etat249,etat250,etat251,etat252,etat253,etat254,etat255,etat235,etat256,etat205,etat206,etat257,etat258,etat219]) (consBan borne264 (consBan borne265 (consBan borne266 (consBan borne267 (consBan borne268 (consBan borne269 (consBan borne270 (consBan borne271 (consBan borne272 (consBan borne273 (consBan borne274 (consBan borne275 (consBan borne255 (consBan borne276 (consBan borne223 (consBan borne224 (consBan borne277 (consBan borne278 (consBan borne238 (nilBan 48 4)))))))))))))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat260 : List ℕ := [valeur163,valeur202,valeur165,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne280 : Ban 48 4 etat260 := viaDirect (by decide +kernel) (by decide +kernel)
def etat261 : List ℕ := [valeur163,valeur203,valeur165,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne281 : Ban 48 4 etat261 := viaDirect (by decide +kernel) (by decide +kernel)
def etat262 : List ℕ := [valeur163,valeur164,valeur176,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne282 : Ban 48 4 etat262 := viaDirect (by decide +kernel) (by decide +kernel)
def etat263 : List ℕ := [valeur163,valeur164,valeur178,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne283 : Ban 48 4 etat263 := viaDirect (by decide +kernel) (by decide +kernel)
def etat264 : List ℕ := [valeur163,valeur164,valeur165,valeur179,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne284 : Ban 48 4 etat264 := viaDirect (by decide +kernel) (by decide +kernel)
def etat265 : List ℕ := [valeur163,valeur164,valeur165,valeur181,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne285 : Ban 48 4 etat265 := viaDirect (by decide +kernel) (by decide +kernel)
def etat266 : List ℕ := [valeur174,valeur163,valeur164,valeur165,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne286 : Ban 48 5 etat266 := viaBranch (ws := [etat260,etat261,etat262,etat263,etat264,etat265,etat207,etat244]) (consBan borne280 (consBan borne281 (consBan borne282 (consBan borne283 (consBan borne284 (consBan borne285 (consBan borne225 (consBan borne264 (nilBan 48 4))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur204 : ℕ := 0xffffe7df5efaffff03f81fc0
def etat267 : List ℕ := [valeur163,valeur164,valeur165,valeur166,valeur167,valeur204]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne287 : Ban 48 5 etat267 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne288 : Ban 48 4 etat259 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur205 : ℕ := 0x9cb265972cb1bc003ffffff
def etat268 : List ℕ := [valeur182,valeur163,valeur205,valeur165,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne289 : Ban 48 4 etat268 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur206 : ℕ := 0x988204122091bc00007e03f
def etat269 : List ℕ := [valeur182,valeur163,valeur206,valeur165,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne290 : Ban 48 4 etat269 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur207 : ℕ := 0x46534e9a55d6c700fff81fff
def etat270 : List ℕ := [valeur163,valeur164,valeur165,valeur207,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne291 : Ban 48 4 etat270 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur208 : ℕ := 0x43061850c2000003f80000
def etat271 : List ℕ := [valeur208,valeur163,valeur164,valeur165,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne292 : Ban 48 4 etat271 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur209 : ℕ := 0xb063973cd8e2f800ffffffc0
def etat272 : List ℕ := [valeur163,valeur164,valeur165,valeur166,valeur209]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne293 : Ban 48 4 etat272 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne294 : Ban 48 5 etat245 := viaBranch (ws := [etat244,etat259,etat268,etat269,etat270,etat271,etat272,etat236,etat208,etat220]) (consBan borne264 (consBan borne288 (consBan borne289 (consBan borne290 (consBan borne291 (consBan borne292 (consBan borne293 (consBan borne256 (consBan borne226 (consBan borne239 (nilBan 48 4))))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat273 : List ℕ := [valeur182,valeur163,valeur164,valeur165,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne295 : Ban 48 5 etat273 := viaDirect (by decide +kernel) (by decide +kernel)
def etat274 : List ℕ := [valeur163,valeur164,valeur165,valeur166,valeur183,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne296 : Ban 48 5 etat274 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur210 : ℕ := 0x3000000103f
def etat275 : List ℕ := [valeur210,valeur163,valeur164,valeur165,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne297 : Ban 48 5 etat275 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur211 : ℕ := 0x4fda6ed3779fdfc0fe07ffff
def etat276 : List ℕ := [valeur163,valeur164,valeur165,valeur211,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne298 : Ban 48 5 etat276 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur212 : ℕ := 0x9ca2651728b18c00207e000
def etat277 : List ℕ := [valeur163,valeur212,valeur164,valeur165,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne299 : Ban 48 5 etat277 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur213 : ℕ := 0x461048820514c400fc000fc0
def etat278 : List ℕ := [valeur163,valeur164,valeur213,valeur165,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne300 : Ban 48 5 etat278 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur214 : ℕ := 0x18000207e000
def etat279 : List ℕ := [valeur214,valeur163,valeur164,valeur165,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne301 : Ban 48 5 etat279 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur215 : ℕ := 0xb9eab775faabfbc0fffff03f
def etat280 : List ℕ := [valeur163,valeur164,valeur165,valeur166,valeur215,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne302 : Ban 48 5 etat280 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur216 : ℕ := 0x9ca2651728b03c00000103f
def etat281 : List ℕ := [valeur163,valeur216,valeur164,valeur165,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne303 : Ban 48 5 etat281 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur217 : ℕ := 0xb02091248820e000fdf80000
def etat282 : List ℕ := [valeur163,valeur164,valeur165,valeur217,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne304 : Ban 48 5 etat282 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur218 : ℕ := 0x988204102081bc000000000
def etat283 : List ℕ := [valeur163,valeur218,valeur164,valeur165,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne305 : Ban 48 5 etat283 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur219 : ℕ := 0xfffee7d77ebbffff0207f03f
def etat284 : List ℕ := [valeur163,valeur164,valeur165,valeur166,valeur167,valeur219]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne306 : Ban 48 5 etat284 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur220 : ℕ := 0x420610708300000207f03f
def etat285 : List ℕ := [valeur220,valeur163,valeur164,valeur165,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne307 : Ban 48 5 etat285 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur221 : ℕ := 0xf634c1860c30e43f00000000
def etat286 : List ℕ := [valeur163,valeur164,valeur165,valeur166,valeur221,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne308 : Ban 48 5 etat286 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur222 : ℕ := 0x43061850c2e4fffff81fc0
def etat287 : List ℕ := [valeur222,valeur164,valeur165,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne309 : Ban 48 4 etat287 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur223 : ℕ := 0x9ca2651728bdbc0fe07f03f
def etat288 : List ℕ := [valeur163,valeur223,valeur165,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne310 : Ban 48 4 etat288 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur224 : ℕ := 0xffbce1c70e38fffffc000000
def etat289 : List ℕ := [valeur163,valeur164,valeur165,valeur166,valeur224]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne311 : Ban 48 4 etat289 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur225 : ℕ := 0xffbce1c70e383fff00000000
def etat290 : List ℕ := [valeur163,valeur164,valeur165,valeur166,valeur225]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne312 : Ban 48 4 etat290 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur226 : ℕ := 0xc000fc000000
def valeur227 : ℕ := 0xf630d9a68d34ff00ffffffff
def etat291 : List ℕ := [valeur226,valeur163,valeur164,valeur227,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne313 : Ban 48 4 etat291 := viaDirect (by decide +kernel) (by decide +kernel)
def etat292 : List ℕ := [valeur226,valeur163,valeur164,valeur165,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne314 : Ban 48 5 etat292 := viaBranch (ws := [etat287,etat288,etat289,etat290,etat291]) (consBan borne309 (consBan borne310 (consBan borne311 (consBan borne312 (consBan borne313 (nilBan 48 4)))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur228 : ℕ := 0x1b000207f03f
def etat293 : List ℕ := [valeur228,valeur163,valeur165,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne315 : Ban 48 4 etat293 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur229 : ℕ := 0xf630d9a68d34e400fdf80fc0
def etat294 : List ℕ := [valeur163,valeur165,valeur166,valeur229,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne316 : Ban 48 4 etat294 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur230 : ℕ := 0xffbcf9e78f3cffffffffffff
def etat295 : List ℕ := [valeur163,valeur164,valeur165,valeur166,valeur230]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne317 : Ban 48 4 etat295 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur231 : ℕ := 0x98c2041020800ff00000000
def etat296 : List ℕ := [valeur163,valeur231,valeur164,valeur165,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne318 : Ban 48 4 etat296 := viaDirect (by decide +kernel) (by decide +kernel)
def etat297 : List ℕ := [valeur163,valeur164,valeur165,valeur166,valeur227,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne319 : Ban 48 5 etat297 := viaBranch (ws := [etat293,etat294,etat291,etat295,etat296]) (consBan borne315 (consBan borne316 (consBan borne313 (consBan borne317 (consBan borne318 (nilBan 48 4)))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur232 : ℕ := 0x461048820514070000001fff
def etat298 : List ℕ := [valeur163,valeur164,valeur232,valeur165,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne320 : Ban 48 5 etat298 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur233 : ℕ := 0xb02091248820380003ffe000
def etat299 : List ℕ := [valeur163,valeur164,valeur165,valeur233,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne321 : Ban 48 5 etat299 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur234 : ℕ := 0x461040820410c70000000000
def etat300 : List ℕ := [valeur163,valeur164,valeur234,valeur165,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne322 : Ban 48 5 etat300 := viaDirect (by decide +kernel) (by decide +kernel)
def etat301 : List ℕ := [valeur163,valeur164,valeur200,valeur166,valeur186]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne323 : Ban 48 4 etat301 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur235 : ℕ := 0x24ff00001fc0
def etat302 : List ℕ := [valeur235,valeur163,valeur164,valeur165,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne324 : Ban 48 4 etat302 := viaDirect (by decide +kernel) (by decide +kernel)
def etat303 : List ℕ := [valeur163,valeur164,valeur165,valeur166,valeur187]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne325 : Ban 48 4 etat303 := viaDirect (by decide +kernel) (by decide +kernel)
def etat304 : List ℕ := [valeur163,valeur164,valeur166,valeur187,valeur186]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne326 : Ban 48 4 etat304 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur236 : ℕ := 0x4f9c68c3071c07ff00001fff
def etat305 : List ℕ := [valeur163,valeur164,valeur165,valeur236,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne327 : Ban 48 4 etat305 := viaDirect (by decide +kernel) (by decide +kernel)
def etat306 : List ℕ := [valeur163,valeur164,valeur165,valeur166,valeur186]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne328 : Ban 48 5 etat306 := viaBranch (ws := [etat212,etat223,etat229,etat301,etat302,etat271,etat303,etat304,etat295,etat305]) (consBan borne230 (consBan borne242 (consBan borne249 (consBan borne323 (consBan borne324 (consBan borne292 (consBan borne325 (consBan borne326 (consBan borne317 (consBan borne327 (nilBan 48 4))))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat307 : List ℕ := [valeur163,valeur164,valeur165,valeur166,valeur167,valeur186]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne329 : Ban 48 5 etat307 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur237 : ℕ := 0x80001040000fc001fff
def etat308 : List ℕ := [valeur237,valeur163,valeur164,valeur165,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne330 : Ban 48 5 etat308 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur238 : ℕ := 0x43061850c2200003f81fc0
def etat309 : List ℕ := [valeur238,valeur163,valeur164,valeur165,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne331 : Ban 48 4 etat309 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur239 : ℕ := 0x4f9c68c3071cc7fffc001fff
def etat310 : List ℕ := [valeur163,valeur164,valeur165,valeur239,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne332 : Ban 48 4 etat310 := viaDirect (by decide +kernel) (by decide +kernel)
def etat311 : List ℕ := [valeur163,valeur164,valeur165,valeur189,valeur188]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne333 : Ban 48 4 etat311 := viaDirect (by decide +kernel) (by decide +kernel)
def etat312 : List ℕ := [valeur163,valeur164,valeur165,valeur166,valeur188]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne334 : Ban 48 4 etat312 := viaDirect (by decide +kernel) (by decide +kernel)
def etat313 : List ℕ := [valeur163,valeur164,valeur165,valeur189,valeur166]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne335 : Ban 48 5 etat313 := viaBranch (ws := [etat215,etat226,etat235,etat309,etat310,etat296,etat311,etat312]) (consBan borne233 (consBan borne245 (consBan borne255 (consBan borne331 (consBan borne332 (consBan borne318 (consBan borne333 (consBan borne334 (nilBan 48 4))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne336 : Ban 48 5 etat303 := viaPerm proj203 proj203 borne335 (by decide +kernel) (by decide +kernel)
def etat314 : List ℕ := [valeur163,valeur164,valeur165,valeur166,valeur187,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne337 : Ban 48 5 etat314 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur240 : ℕ := 0xb02081040820f80000000000
def etat315 : List ℕ := [valeur163,valeur164,valeur165,valeur240,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne338 : Ban 48 5 etat315 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne339 : Ban 48 5 etat312 := viaPerm proj203 proj203 borne328 (by decide +kernel) (by decide +kernel)
def etat316 : List ℕ := [valeur163,valeur164,valeur165,valeur166,valeur167,valeur188]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne340 : Ban 48 5 etat316 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur241 : ℕ := 0x102080000000ffffe000
def etat317 : List ℕ := [valeur241,valeur163,valeur164,valeur165,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne341 : Ban 48 5 etat317 := viaDirect (by decide +kernel) (by decide +kernel)
def etat318 : List ℕ := [valeur163,valeur164,valeur165,valeur189,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne342 : Ban 48 5 etat318 := viaDirect (by decide +kernel) (by decide +kernel)
def etat319 : List ℕ := [valeur163,valeur164,valeur165,valeur166,valeur167]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne343 : Ban 48 6 etat319 := viaBranch (ws := [etat186,etat216,etat217,etat218,etat187,etat227,etat228,etat232,etat239,etat240,etat241,etat242,etat238,etat243,etat259,etat266,etat267,etat245,etat273,etat274,etat275,etat276,etat277,etat278,etat279,etat280,etat281,etat282,etat283,etat284,etat285,etat286,etat292,etat297,etat298,etat299,etat300,etat306,etat307,etat308,etat303,etat314,etat315,etat312,etat316,etat317,etat313,etat318]) (consBan borne204 (consBan borne234 (consBan borne235 (consBan borne236 (consBan borne246 (consBan borne247 (consBan borne248 (consBan borne252 (consBan borne259 (consBan borne260 (consBan borne261 (consBan borne262 (consBan borne258 (consBan borne263 (consBan borne279 (consBan borne286 (consBan borne287 (consBan borne294 (consBan borne295 (consBan borne296 (consBan borne297 (consBan borne298 (consBan borne299 (consBan borne300 (consBan borne301 (consBan borne302 (consBan borne303 (consBan borne304 (consBan borne305 (consBan borne306 (consBan borne307 (consBan borne308 (consBan borne314 (consBan borne319 (consBan borne320 (consBan borne321 (consBan borne322 (consBan borne328 (consBan borne329 (consBan borne330 (consBan borne336 (consBan borne337 (consBan borne338 (consBan borne339 (consBan borne340 (consBan borne341 (consBan borne335 (consBan borne342 (nilBan 48 5))))))))))))))))))))))))))))))))))))))))))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne344 : Wide 48 6 etat319 := widen (by decide +kernel) borne343
def valeur242 : ℕ := 0x20008002000800200080020008002000800200080020008002000800200080020008002000800200080020008000000000000000fffc000000000000000000000000fffc000000000000000000003ffffffc00000000000000000
def etat320 : List ℕ := [valeur67,valeur242,valeur68,valeur69,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne345 : Ban 364 7 etat320 := viaCut proj2 borne344 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur243 : ℕ := 0x4bc12f04bc12f04bc12f04bc12f04bc12f04bc12f04bc12f04bc12f04bc12f04bc12f04bc12f04bc12f04bc12f0fffffff0000000fffffffffffffffffffff0000000ffffffffffffff00000000003ffffffffffffffffffffffff
def etat321 : List ℕ := [valeur67,valeur68,valeur69,valeur70,valeur243,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne346 : Ban 364 7 etat321 := viaCut proj2 borne344 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur244 : ℕ := 0x8c023008c023008c023008c023008c023008c023008c023008c023008c023008c023008c023008c023008c02300003fff000000000000000003ffffffffff00000000000000fffffff0000000000000000000000000000fffffff
def etat322 : List ℕ := [valeur67,valeur244,valeur68,valeur69,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne347 : Ban 364 7 etat322 := viaCut proj2 borne344 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur245 : ℕ := 0x4101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040fffc00000000000003ffffffc000000000000000000003fff0000000000000000000000003ffffffffff0000000
def etat323 : List ℕ := [valeur67,valeur68,valeur69,valeur245,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne348 : Ban 364 7 etat323 := viaCut proj2 borne344 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur246 : ℕ := 0x8002000800200080020008002000800200080020008002000800200080020008002000800200080020008002000003fff00000000000000000000000000000000000fffc000fffffff00000000000000000000000000000000000
def etat324 : List ℕ := [valeur67,valeur246,valeur68,valeur69,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne349 : Ban 364 7 etat324 := viaCut proj2 borne344 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur247 : ℕ := 0x8ec23b08ec23b08ec23b08ec23b08ec23b08ec23b08ec23b08ec23b08ec23b08ec23b08ec23b08ec23b08ec23b0fffffffffffffffffc0000003ffffffffff0000000fffffffffffffffffffffffffffffffc0000000000fffffff
def etat325 : List ℕ := [valeur67,valeur68,valeur69,valeur70,valeur71,valeur247,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne350 : Ban 364 7 etat325 := viaCut proj2 borne344 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur248 : ℕ := 0x2c00b002c00b002c00b002c00b002c00b002c00b002c00b002c00b002c00b002c00b002c00b002c00b002c00b000000000000000fffc0000003ffffffffff00000000000000000000000000000003ffffffc0000000000fffffff
def etat326 : List ℕ := [valeur67,valeur248,valeur68,valeur69,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne351 : Ban 364 7 etat326 := viaCut proj2 borne344 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur249 : ℕ := 0x8402100840210084021008402100840210084021008402100840210084021008402100840210084021008402100fffc000fffffff00000000000000000000000000000003fff0000000ffffffffffc000000000000000000000000
def etat327 : List ℕ := [valeur67,valeur68,valeur69,valeur70,valeur249,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne352 : Ban 364 7 etat327 := viaCut proj2 borne344 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur250 : ℕ := 0x3fff0000000fffc0000003ffffffffff00000000000000000000000000000000000000000000000000000000
def etat328 : List ℕ := [valeur250,valeur67,valeur68,valeur69,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne353 : Ban 364 7 etat328 := viaCut proj2 borne344 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur251 : ℕ := 0xfac3eb0fac3eb0fac3eb0fac3eb0fac3eb0fac3eb0fac3eb0fac3eb0fac3eb0fac3eb0fac3eb0fac3eb0fac3eb0fffffffffffffffffffffffffffffffffffffffffffffc000fffffff00000000003ffffffc0000000000fffffff
def etat329 : List ℕ := [valeur67,valeur68,valeur69,valeur70,valeur71,valeur72,valeur251]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne354 : Ban 364 7 etat329 := viaCut proj2 borne344 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur252 : ℕ := 0xac02b00ac02b00ac02b00ac02b00ac02b00ac02b00ac02b00ac02b00ac02b00ac02b00ac02b00ac02b00ac02b0000000000000000000000000000000000000000000fffc000fffffff00000000003ffffffc0000000000fffffff
def etat330 : List ℕ := [valeur67,valeur252,valeur68,valeur69,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne355 : Ban 364 7 etat330 := viaCut proj2 borne344 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur253 : ℕ := 0xf003c00f003c00f003c00f003c00f003c00f003c00f003c00f003c00f003c00f003c00f003c00f003c00f003c00fffc000fffffff0003ffffffc0000000000fffffff0000000000000000000000000000000000000000000000000
def etat331 : List ℕ := [valeur67,valeur68,valeur69,valeur70,valeur71,valeur253,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne356 : Ban 364 7 etat331 := viaCut proj2 borne344 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur254 : ℕ := 0xfffc000000000000000000000000000000000000000000000fffffff0003fff0000000
def etat332 : List ℕ := [valeur254,valeur67,valeur68,valeur69,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne357 : Ban 364 7 etat332 := viaCut proj0 borne181 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur255 : ℕ := 0x63298ca63298ca63298ca63298ca63298ca63298ca63298ca63298ca63298ca63298ca63298ca63298ca63298cafffc0000003fffffffffffffc000fffc000fffc000fffffff0003ffffffc000ffffffffffffffffffffffffffff
def etat333 : List ℕ := [valeur67,valeur68,valeur69,valeur70,valeur255,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne358 : Ban 364 7 etat333 := viaCut proj0 borne181 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur256 : ℕ := 0x202880a202880a202880a202880a202880a202880a202880a202880a202880a202880a202880a202880a202880a00000000003fff00000000000000fffc000fffc00000000000003ffffffc000fffc00000000000000000fffffff
def etat334 : List ℕ := [valeur67,valeur68,valeur256,valeur69,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne359 : Ban 364 7 etat334 := viaCut proj0 borne181 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur257 : ℕ := 0x43010c043010c043010c043010c043010c043010c043010c043010c043010c043010c043010c043010c043010c0fffc0000000000fffffff000000000000000000000fffffff000000000000000003fff0000000fffc0000000000
def etat335 : List ℕ := [valeur67,valeur68,valeur69,valeur257,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne360 : Ban 364 7 etat335 := viaCut proj0 borne181 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur258 : ℕ := 0x3fff000000000000000000000000000000000000003ffffffc000fffc000000000000000000000000
def etat336 : List ℕ := [valeur258,valeur67,valeur68,valeur69,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne361 : Ban 364 7 etat336 := viaCut proj0 borne181 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur259 : ℕ := 0xac2ab0aac2ab0aac2ab0aac2ab0aac2ab0aac2ab0aac2ab0aac2ab0aac2ab0aac2ab0aac2ab0aac2ab0aac2ab0affffffffffffff0000000fffc000fffc000fffc000ffffffffffffffffffffffffc000fffffff0003ffffffffff
def etat337 : List ℕ := [valeur67,valeur68,valeur69,valeur70,valeur71,valeur259,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne362 : Ban 364 7 etat337 := viaCut proj0 borne181 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur260 : ℕ := 0x202880a202880a202880a202880a202880a202880a202880a202880a202880a202880a202880a202880a202880a000000000000000000000fffc000fffc000fffc0000000000000000000000000000000fffffff0003ffffffffff
def etat338 : List ℕ := [valeur67,valeur68,valeur260,valeur69,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne363 : Ban 364 7 etat338 := viaCut proj0 borne181 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur261 : ℕ := 0x8c023008c023008c023008c023008c023008c023008c023008c023008c023008c023008c023008c023008c02300ffffffffffc0000000000000000000000000000000ffffffffffc0000003fff0000000000000000000000000000
def etat339 : List ℕ := [valeur67,valeur68,valeur69,valeur70,valeur261,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne364 : Ban 364 7 etat339 := viaCut proj0 borne181 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur262 : ℕ := 0x200080020008002000800200080020008002000800200080020008002000800200080020008002000800200080000000000003fff0000000fffc000fffc000fffc0000000000000000000000000000000000000000000000000000
def etat340 : List ℕ := [valeur67,valeur68,valeur262,valeur69,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne365 : Ban 364 7 etat340 := viaCut proj0 borne181 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur263 : ℕ := 0xf02bc0af02bc0af02bc0af02bc0af02bc0af02bc0af02bc0af02bc0af02bc0af02bc0af02bc0af02bc0af02bc0affffffffffffffffffffffffffffffffffffffffff00000000003ffffffc000fffc000fffffff0003ffffffffff
def etat341 : List ℕ := [valeur67,valeur68,valeur69,valeur70,valeur71,valeur72,valeur263]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne366 : Ban 364 7 etat341 := viaCut proj0 borne181 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur264 : ℕ := 0x2800a002800a002800a002800a002800a002800a002800a002800a002800a002800a002800a002800a002800a00000000000000000000000000000000000000000000000000003ffffffc000fffc000fffffff0003ffffffffff
def etat342 : List ℕ := [valeur264,valeur67,valeur68,valeur69,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne367 : Ban 364 7 etat342 := viaCut proj0 borne181 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur265 : ℕ := 0xd003400d003400d003400d003400d003400d003400d003400d003400d003400d003400d003400d003400d003400ffffffffffc000fffffff0003fff0003fff0003fff0000000000000000000000000000000000000000000000000
def etat343 : List ℕ := [valeur67,valeur68,valeur69,valeur70,valeur71,valeur265,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne368 : Ban 364 7 etat343 := viaCut proj0 borne181 (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj369 : Projection 50 50 := pick [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj370 : Projection 50 50 := pick [9,14,12,15,13,10,11,45,46,0,5,6,2,4,1,3,40,41,42,37,39,36,38,43,24,49,48,31,32,33,30,27,28,29,35,34,21,19,22,20,16,17,18,23,47,7,8,44,26,25] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj371 : Projection 50 50 := pick [27,28,31,32,33,29,30,34,35,16,17,21,19,22,18,20,9,10,14,12,15,11,13,23,47,45,46,0,1,5,6,2,3,4,7,8,36,40,41,42,37,38,39,44,43,25,26,24,49,48] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj372 : Projection 50 50 := pick [16,18,19,20,22,17,21,25,26,27,29,30,31,33,28,32,37,38,39,40,42,36,41,44,47,48,49,2,3,4,6,0,1,5,8,7,11,12,13,15,9,10,14,23,24,34,35,43,46,45] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj373 : Projection 50 50 := pick [2,3,0,1,5,4,6,8,7,37,38,36,40,41,39,42,27,29,28,31,32,30,33,44,43,34,35,16,18,17,21,19,20,22,25,26,11,9,10,14,12,13,15,24,23,48,49,47,45,46] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj374 : Projection 50 50 := pick [37,39,40,42,41,38,36,48,49,2,4,6,0,5,3,1,12,13,15,9,14,11,10,24,43,46,45,19,20,22,21,16,18,17,26,25,30,31,33,32,27,29,28,44,47,8,7,23,35,34] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj375 : Projection 50 50 := pick [19,20,16,18,17,22,21,26,25,12,13,11,9,10,15,14,2,4,3,0,1,6,5,24,23,8,7,37,39,38,36,40,42,41,48,49,30,27,29,28,31,33,32,47,44,46,45,43,34,35] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj376 : Projection 50 50 := pick [12,15,9,14,10,13,11,46,45,19,22,21,16,17,20,18,31,33,32,27,28,30,29,47,23,35,34,40,42,41,36,37,39,38,49,48,6,0,5,1,2,4,3,24,43,26,25,44,7,8] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj377 : Projection 50 50 := pick [31,32,27,28,29,33,30,35,34,40,41,36,37,38,42,39,0,5,1,2,3,6,4,43,44,7,8,9,14,10,11,12,15,13,45,46,21,16,17,18,19,22,20,47,23,49,48,24,25,26] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj378 : Projection 50 50 := pick [40,42,37,39,38,41,36,49,48,31,33,30,27,29,32,28,19,22,20,16,18,21,17,47,44,26,25,12,15,13,11,9,14,10,46,45,6,2,4,3,0,5,1,43,24,35,34,23,8,7] rfl (by decide +kernel) (by decide)
def valeur266 : ℕ := 0x5042081208000c00800180
def valeur267 : ℕ := 0x4150ea1c3628900ffeff0180
def valeur268 : ℕ := 0xa87442891a8c680c0180ffff
def valeur269 : ℕ := 0x443819c50a4731ff0070001ff
def valeur270 : ℕ := 0xbbc2e01830183fffff8000000
def valeur271 : ℕ := 0xf12091562c143e00007fffe00
def etat344 : List ℕ := [valeur266,valeur267,valeur268,valeur269,valeur270,valeur271]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne379 : Ban 50 5 etat344 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur272 : ℕ := 0xe974ea9d3eacf80fffffffff
def etat345 : List ℕ := [valeur267,valeur268,valeur272,valeur269,valeur270,valeur271]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne380 : Ban 50 5 etat345 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur273 : ℕ := 0x4100a81424209003fe7f0000
def etat346 : List ℕ := [valeur273,valeur267,valeur268,valeur269,valeur270,valeur271]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne381 : Ban 50 5 etat346 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur274 : ℕ := 0xa8240081088468000100fe7f
def etat347 : List ℕ := [valeur267,valeur274,valeur268,valeur269,valeur270,valeur271]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne382 : Ban 50 5 etat347 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur275 : ℕ := 0x410088102420100006000180
def etat348 : List ℕ := [valeur275,valeur267,valeur268,valeur269,valeur270,valeur271]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne383 : Ban 50 5 etat348 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur276 : ℕ := 0x443d1fe5cb67b9fffffff01ff
def etat349 : List ℕ := [valeur267,valeur268,valeur269,valeur276,valeur270,valeur271]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne384 : Ban 50 5 etat349 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur277 : ℕ := 0x50620c1208800ff8ff0000
def etat350 : List ℕ := [valeur277,valeur267,valeur268,valeur269,valeur270,valeur271]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne385 : Ban 50 5 etat350 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur278 : ℕ := 0x40281144080530ff00100007f
def etat351 : List ℕ := [valeur267,valeur268,valeur278,valeur269,valeur270,valeur271]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne386 : Ban 50 5 etat351 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur279 : ℕ := 0x900ff8000000
def etat352 : List ℕ := [valeur279,valeur267,valeur268,valeur269,valeur270,valeur271]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne387 : Ban 50 5 etat352 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur280 : ℕ := 0xbfd7eeb9f37abfffffeff0180
def etat353 : List ℕ := [valeur267,valeur268,valeur269,valeur270,valeur280,valeur271]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne388 : Ban 50 5 etat353 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur281 : ℕ := 0x4150ea1c3628000006ff0180
def etat354 : List ℕ := [valeur281,valeur267,valeur268,valeur269,valeur270,valeur271]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne389 : Ban 50 5 etat354 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur282 : ℕ := 0xbbc2e018301836ff000000000
def etat355 : List ℕ := [valeur267,valeur268,valeur269,valeur282,valeur270,valeur271]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne390 : Ban 50 5 etat355 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur283 : ℕ := 0x800006ff0000
def etat356 : List ℕ := [valeur283,valeur267,valeur268,valeur269,valeur270,valeur271]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne391 : Ban 50 5 etat356 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur284 : ℕ := 0xf5359ff7ef76bf00fffffff80
def etat357 : List ℕ := [valeur267,valeur268,valeur269,valeur270,valeur271,valeur284]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne392 : Ban 50 5 etat357 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur285 : ℕ := 0x4150ea1c3628100ff8000180
def etat358 : List ℕ := [valeur285,valeur267,valeur268,valeur269,valeur270,valeur271]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne393 : Ban 50 5 etat358 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur286 : ℕ := 0xf12091562c14360000100fe00
def etat359 : List ℕ := [valeur267,valeur268,valeur269,valeur270,valeur286,valeur271]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne394 : Ban 50 5 etat359 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur287 : ℕ := 0x800010001ff
def etat360 : List ℕ := [valeur287,valeur267,valeur268,valeur269,valeur270,valeur271]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne395 : Ban 50 5 etat360 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur288 : ℕ := 0x4ebf5ded9beff7ffc0780ffff
def etat361 : List ℕ := [valeur267,valeur268,valeur269,valeur288,valeur270,valeur271]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne396 : Ban 50 5 etat361 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur289 : ℕ := 0xa87442891a8c600c0080fe00
def etat362 : List ℕ := [valeur267,valeur289,valeur268,valeur269,valeur270,valeur271]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne397 : Ban 50 5 etat362 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur290 : ℕ := 0x443819c50a47317f006000000
def etat363 : List ℕ := [valeur267,valeur268,valeur290,valeur269,valeur270,valeur271]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne398 : Ban 50 5 etat363 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur291 : ℕ := 0xa82400810080680c00000000
def etat364 : List ℕ := [valeur267,valeur291,valeur268,valeur269,valeur270,valeur271]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne399 : Ban 50 5 etat364 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur292 : ℕ := 0xbbc7e438b1b8ffffff980ffff
def etat365 : List ℕ := [valeur267,valeur268,valeur269,valeur270,valeur292,valeur271]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne400 : Ban 50 5 etat365 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur293 : ℕ := 0x5042081a0c00000180ffff
def etat366 : List ℕ := [valeur293,valeur267,valeur268,valeur269,valeur270,valeur271]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne401 : Ban 50 5 etat366 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur294 : ℕ := 0xb140a0102010397f3f8000000
def etat367 : List ℕ := [valeur267,valeur268,valeur269,valeur294,valeur270,valeur271]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne402 : Ban 50 5 etat367 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur295 : ℕ := 0x60000180fe00
def etat368 : List ℕ := [valeur295,valeur267,valeur268,valeur269,valeur270,valeur271]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne403 : Ban 50 5 etat368 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur296 : ℕ := 0xfba7d57ebdbcfe80c07ffffff
def etat369 : List ℕ := [valeur267,valeur268,valeur269,valeur270,valeur271,valeur296]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne404 : Ban 50 5 etat369 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur297 : ℕ := 0xa87442891a8c080c000001ff
def etat370 : List ℕ := [valeur267,valeur297,valeur268,valeur269,valeur270,valeur271]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne405 : Ban 50 5 etat370 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur298 : ℕ := 0xf12091562c1438000067f0000
def etat371 : List ℕ := [valeur267,valeur268,valeur269,valeur270,valeur298,valeur271]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne406 : Ban 50 5 etat371 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur299 : ℕ := 0x31ff000000000
def etat372 : List ℕ := [valeur299,valeur267,valeur268,valeur269,valeur270,valeur271]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne407 : Ban 50 5 etat372 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur300 : ℕ := 0xfffaf9dd3a5f3ffffff0001ff
def etat373 : List ℕ := [valeur267,valeur268,valeur269,valeur270,valeur271,valeur300]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne408 : Ban 50 5 etat373 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur301 : ℕ := 0x443819c50a4700000070001ff
def etat374 : List ℕ := [valeur267,valeur268,valeur301,valeur269,valeur270,valeur271]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne409 : Ban 50 5 etat374 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur302 : ℕ := 0xbbc2e01830180e00ff8000000
def etat375 : List ℕ := [valeur267,valeur268,valeur269,valeur302,valeur270,valeur271]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne410 : Ban 50 5 etat375 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur303 : ℕ := 0x4020114408043000007000000
def etat376 : List ℕ := [valeur267,valeur268,valeur303,valeur269,valeur270,valeur271]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne411 : Ban 50 5 etat376 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur304 : ℕ := 0xf53899d72e573fff007ffffff
def etat377 : List ℕ := [valeur267,valeur268,valeur269,valeur270,valeur271,valeur304]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne412 : Ban 50 5 etat377 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur305 : ℕ := 0x4180881024301ff0000001ff
def etat378 : List ℕ := [valeur267,valeur305,valeur268,valeur269,valeur270,valeur271]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne413 : Ban 50 5 etat378 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur306 : ℕ := 0xb100801224100e00000fffe00
def etat379 : List ℕ := [valeur267,valeur268,valeur269,valeur306,valeur270,valeur271]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne414 : Ban 50 5 etat379 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur307 : ℕ := 0xb100801020103e00000000000
def etat380 : List ℕ := [valeur267,valeur268,valeur269,valeur307,valeur270,valeur271]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne415 : Ban 50 5 etat380 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur308 : ℕ := 0xfbe2f15e3c1c3fffffffffe00
def etat381 : List ℕ := [valeur267,valeur268,valeur269,valeur270,valeur271,valeur308]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne416 : Ban 50 5 etat381 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur309 : ℕ := 0xac26008100801ffff8000000
def etat382 : List ℕ := [valeur267,valeur268,valeur309,valeur269,valeur270,valeur271]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne417 : Ban 50 5 etat382 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur310 : ℕ := 0x402011460c040000007fffe00
def etat383 : List ℕ := [valeur267,valeur268,valeur310,valeur269,valeur270,valeur271]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne418 : Ban 50 5 etat383 := viaDirect (by decide +kernel) (by decide +kernel)
def etat384 : List ℕ := [valeur267,valeur268,valeur269,valeur270,valeur271]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne419 : Ban 50 6 etat384 := viaBranch (ws := [etat344,etat345,etat346,etat347,etat348,etat349,etat350,etat351,etat352,etat353,etat354,etat355,etat356,etat357,etat358,etat359,etat360,etat361,etat362,etat363,etat364,etat365,etat366,etat367,etat368,etat369,etat370,etat371,etat372,etat373,etat374,etat375,etat376,etat377,etat378,etat379,etat380,etat381,etat382,etat383]) (consBan borne379 (consBan borne380 (consBan borne381 (consBan borne382 (consBan borne383 (consBan borne384 (consBan borne385 (consBan borne386 (consBan borne387 (consBan borne388 (consBan borne389 (consBan borne390 (consBan borne391 (consBan borne392 (consBan borne393 (consBan borne394 (consBan borne395 (consBan borne396 (consBan borne397 (consBan borne398 (consBan borne399 (consBan borne400 (consBan borne401 (consBan borne402 (consBan borne403 (consBan borne404 (consBan borne405 (consBan borne406 (consBan borne407 (consBan borne408 (consBan borne409 (consBan borne410 (consBan borne411 (consBan borne412 (consBan borne413 (consBan borne414 (consBan borne415 (consBan borne416 (consBan borne417 (consBan borne418 (nilBan 50 5))))))))))))))))))))))))))))))))))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne420 : Wide 50 6 etat384 := widen (by decide +kernel) borne419
def valeur311 : ℕ := 0xfffc00000000000000000000000000000000000000fffffff000000000000000000000000000000000000000000
def etat385 : List ℕ := [valeur311,valeur67,valeur68,valeur69,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne421 : Ban 364 7 etat385 := viaCut proj3 borne420 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur312 : ℕ := 0xcf033c0cf033c0cf033c0cf033c0cf033c0cf033c0cf033c0cf033c0cf033c0cf033c0cf033c0cf033c0cf033c0ffffffffffffffffffffffffc00000000000000000ffffffffffffffffffffffffffffffffffffffffff0000000
def etat386 : List ℕ := [valeur67,valeur68,valeur69,valeur70,valeur71,valeur312,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne422 : Ban 364 7 etat386 := viaCut proj3 borne420 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur313 : ℕ := 0x43010c043010c043010c043010c043010c043010c043010c043010c043010c043010c043010c043010c043010c000000000000000ffffffffffc000000000000000000000000000000000000000003fffffffffffffffff0000000
def etat387 : List ℕ := [valeur67,valeur68,valeur69,valeur313,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne423 : Ban 364 7 etat387 := viaCut proj3 borne420 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur314 : ℕ := 0x8c023008c023008c023008c023008c023008c023008c023008c023008c023008c023008c023008c023008c023000003ffffffffff00000000000000000000000000000000000fffffffffffffffffc000000000000000000000000
def etat388 : List ℕ := [valeur67,valeur68,valeur69,valeur70,valeur314,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne424 : Ban 364 7 etat388 := viaCut proj3 borne420 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur315 : ℕ := 0x4001000400100040010004001000400100040010004001000400100040010004001000400100040010004001000fffc0000000000ffffffffffc000000000000000000000000000000000000000000000000000000000000000000
def etat389 : List ℕ := [valeur67,valeur68,valeur69,valeur315,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne425 : Ban 364 7 etat389 := viaCut proj3 borne420 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur316 : ℕ := 0xf303cc0f303cc0f303cc0f303cc0f303cc0f303cc0f303cc0f303cc0f303cc0f303cc0f303cc0f303cc0f303cc0fffffffffffffffffffffffffffffffffffffffffffffffff000000000000000003fffffffffffffffff0000000
def etat390 : List ℕ := [valeur67,valeur68,valeur69,valeur70,valeur71,valeur72,valeur316]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne426 : Ban 364 7 etat390 := viaCut proj3 borne420 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur317 : ℕ := 0x3000c003000c003000c003000c003000c003000c003000c003000c003000c003000c003000c003000c003000c0000000000000000000000000000000000000000000fffffff000000000000000003fffffffffffffffff0000000
def etat391 : List ℕ := [valeur67,valeur317,valeur68,valeur69,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne427 : Ban 364 7 etat391 := viaCut proj3 borne420 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur318 : ℕ := 0xb002c00b002c00b002c00b002c00b002c00b002c00b002c00b002c00b002c00b002c00b002c00b002c00b002c000003ffffffffff00000000003fffffffffffffffff0000000000000000000000000000000000000000000000000
def etat392 : List ℕ := [valeur67,valeur68,valeur69,valeur70,valeur71,valeur318,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne428 : Ban 364 7 etat392 := viaCut proj3 borne420 (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj429 : Projection 50 50 := pick [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj430 : Projection 50 50 := pick [9,14,12,15,13,10,11,45,46,0,5,6,2,4,1,3,40,41,42,37,39,36,38,43,24,49,48,31,32,33,30,27,28,29,35,34,21,19,22,20,16,17,18,23,47,7,8,44,26,25] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj431 : Projection 50 50 := pick [27,28,31,32,33,29,30,34,35,16,17,21,19,22,18,20,9,10,14,12,15,11,13,23,47,45,46,0,1,5,6,2,3,4,7,8,36,40,41,42,37,38,39,44,43,25,26,24,49,48] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj432 : Projection 50 50 := pick [16,18,19,20,22,17,21,25,26,27,29,30,31,33,28,32,37,38,39,40,42,36,41,44,47,48,49,2,3,4,6,0,1,5,8,7,11,12,13,15,9,10,14,23,24,34,35,43,46,45] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj433 : Projection 50 50 := pick [2,3,0,1,5,4,6,8,7,37,38,36,40,41,39,42,27,29,28,31,32,30,33,44,43,34,35,16,18,17,21,19,20,22,25,26,11,9,10,14,12,13,15,24,23,48,49,47,45,46] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj434 : Projection 50 50 := pick [37,39,40,42,41,38,36,48,49,2,4,6,0,5,3,1,12,13,15,9,14,11,10,24,43,46,45,19,20,22,21,16,18,17,26,25,30,31,33,32,27,29,28,44,47,8,7,23,35,34] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj435 : Projection 50 50 := pick [19,20,16,18,17,22,21,26,25,12,13,11,9,10,15,14,2,4,3,0,1,6,5,24,23,8,7,37,39,38,36,40,42,41,48,49,30,27,29,28,31,33,32,47,44,46,45,43,34,35] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj436 : Projection 50 50 := pick [12,15,9,14,10,13,11,46,45,19,22,21,16,17,20,18,31,33,32,27,28,30,29,47,23,35,34,40,42,41,36,37,39,38,49,48,6,0,5,1,2,4,3,24,43,26,25,44,7,8] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj437 : Projection 50 50 := pick [31,32,27,28,29,33,30,35,34,40,41,36,37,38,42,39,0,5,1,2,3,6,4,43,44,7,8,9,14,10,11,12,15,13,45,46,21,16,17,18,19,22,20,47,23,49,48,24,25,26] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj438 : Projection 50 50 := pick [40,42,37,39,38,41,36,49,48,31,33,30,27,29,32,28,19,22,20,16,18,21,17,47,44,26,25,12,15,13,11,9,14,10,46,45,6,2,4,3,0,5,1,43,24,35,34,23,8,7] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne439 : Ban 50 5 etat344 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne440 : Ban 50 5 etat345 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne441 : Ban 50 5 etat346 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne442 : Ban 50 5 etat347 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne443 : Ban 50 5 etat348 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne444 : Ban 50 5 etat349 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne445 : Ban 50 5 etat350 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne446 : Ban 50 5 etat351 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne447 : Ban 50 5 etat352 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne448 : Ban 50 5 etat353 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne449 : Ban 50 5 etat354 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne450 : Ban 50 5 etat355 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne451 : Ban 50 5 etat356 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne452 : Ban 50 5 etat357 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne453 : Ban 50 5 etat358 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne454 : Ban 50 5 etat359 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne455 : Ban 50 5 etat360 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne456 : Ban 50 5 etat361 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne457 : Ban 50 5 etat362 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne458 : Ban 50 5 etat363 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne459 : Ban 50 5 etat364 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne460 : Ban 50 5 etat365 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne461 : Ban 50 5 etat366 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne462 : Ban 50 5 etat367 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne463 : Ban 50 5 etat368 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne464 : Ban 50 5 etat369 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne465 : Ban 50 5 etat370 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne466 : Ban 50 5 etat371 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne467 : Ban 50 5 etat372 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne468 : Ban 50 5 etat373 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne469 : Ban 50 5 etat374 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne470 : Ban 50 5 etat375 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne471 : Ban 50 5 etat376 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne472 : Ban 50 5 etat377 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne473 : Ban 50 5 etat378 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne474 : Ban 50 5 etat379 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne475 : Ban 50 5 etat380 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne476 : Ban 50 5 etat381 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne477 : Ban 50 5 etat382 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne478 : Ban 50 5 etat383 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne479 : Ban 50 6 etat384 := viaBranch (ws := [etat344,etat345,etat346,etat347,etat348,etat349,etat350,etat351,etat352,etat353,etat354,etat355,etat356,etat357,etat358,etat359,etat360,etat361,etat362,etat363,etat364,etat365,etat366,etat367,etat368,etat369,etat370,etat371,etat372,etat373,etat374,etat375,etat376,etat377,etat378,etat379,etat380,etat381,etat382,etat383]) (consBan borne439 (consBan borne440 (consBan borne441 (consBan borne442 (consBan borne443 (consBan borne444 (consBan borne445 (consBan borne446 (consBan borne447 (consBan borne448 (consBan borne449 (consBan borne450 (consBan borne451 (consBan borne452 (consBan borne453 (consBan borne454 (consBan borne455 (consBan borne456 (consBan borne457 (consBan borne458 (consBan borne459 (consBan borne460 (consBan borne461 (consBan borne462 (consBan borne463 (consBan borne464 (consBan borne465 (consBan borne466 (consBan borne467 (consBan borne468 (consBan borne469 (consBan borne470 (consBan borne471 (consBan borne472 (consBan borne473 (consBan borne474 (consBan borne475 (consBan borne476 (consBan borne477 (consBan borne478 (nilBan 50 5))))))))))))))))))))))))))))))))))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne480 : Wide 50 6 etat384 := widen (by decide +kernel) borne479
def valeur319 : ℕ := 0x8002000800200080020008002000800200080020008002000800200080020008002000800200080020008002000ffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000
def etat393 : List ℕ := [valeur67,valeur68,valeur69,valeur70,valeur319,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne481 : Ban 364 7 etat393 := viaCut proj4 borne480 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur320 : ℕ := 0xfc03f00fc03f00fc03f00fc03f00fc03f00fc03f00fc03f00fc03f00fc03f00fc03f00fc03f00fc03f00fc03f00ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000000000000000000000000
def etat394 : List ℕ := [valeur67,valeur68,valeur69,valeur70,valeur71,valeur72,valeur320]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne482 : Ban 364 7 etat394 := viaCut proj4 borne480 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur321 : ℕ := 0xc003000c003000c003000c003000c003000c003000c003000c003000c003000c003000c003000c003000c00300000000000000000000000000000000000000000000ffffffffffffffffffffffffc000000000000000000000000
def etat395 : List ℕ := [valeur67,valeur68,valeur321,valeur69,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne483 : Ban 364 7 etat395 := viaCut proj4 borne480 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur322 : ℕ := 0x7001c007001c007001c007001c007001c007001c007001c007001c007001c007001c007001c007001c007001c0000000000000000ffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000
def etat396 : List ℕ := [valeur67,valeur68,valeur69,valeur70,valeur322,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne484 : Ban 364 7 etat396 := viaCut proj4 borne480 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat397 : List ℕ := [valeur67,valeur68,valeur69,valeur70,valeur71,valeur72]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne485 : Ban 364 8 etat397 := viaBranch (ws := [etat81,etat82,etat83,etat84,etat166,etat167,etat168,etat169,etat170,etat171,etat172,etat173,etat174,etat175,etat176,etat177,etat178,etat179,etat180,etat181,etat182,etat183,etat184,etat185,etat320,etat321,etat322,etat323,etat324,etat325,etat326,etat327,etat328,etat329,etat330,etat331,etat332,etat333,etat334,etat335,etat336,etat337,etat338,etat339,etat340,etat341,etat342,etat343,etat385,etat386,etat387,etat388,etat389,etat390,etat391,etat392,etat393,etat394,etat395,etat396]) (consBan borne92 (consBan borne93 (consBan borne94 (consBan borne95 (consBan borne182 (consBan borne183 (consBan borne184 (consBan borne185 (consBan borne186 (consBan borne187 (consBan borne188 (consBan borne189 (consBan borne190 (consBan borne191 (consBan borne192 (consBan borne193 (consBan borne194 (consBan borne195 (consBan borne196 (consBan borne197 (consBan borne198 (consBan borne199 (consBan borne200 (consBan borne201 (consBan borne345 (consBan borne346 (consBan borne347 (consBan borne348 (consBan borne349 (consBan borne350 (consBan borne351 (consBan borne352 (consBan borne353 (consBan borne354 (consBan borne355 (consBan borne356 (consBan borne357 (consBan borne358 (consBan borne359 (consBan borne360 (consBan borne361 (consBan borne362 (consBan borne363 (consBan borne364 (consBan borne365 (consBan borne366 (consBan borne367 (consBan borne368 (consBan borne421 (consBan borne422 (consBan borne423 (consBan borne424 (consBan borne425 (consBan borne426 (consBan borne427 (consBan borne428 (consBan borne481 (consBan borne482 (consBan borne483 (consBan borne484 (nilBan 364 7))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne486 : Wide 364 8 etat397 := widen (by decide +kernel) borne485
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj487 : Projection 365 364 := pick [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255,256,257,258,259,260,261,262,263,264,265,266,267,268,269,270,271,272,273,274,275,276,277,278,279,280,281,282,283,284,285,286,287,288,289,290,291,292,293,294,295,296,297,298,299,300,301,302,303,304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319,320,321,322,323,324,325,326,327,328,329,330,331,332,333,334,335,336,337,338,339,340,341,342,343,344,345,346,347,348,349,350,351,352,353,354,355,356,357,358,359,360,361,362,363] rfl (by decide +kernel) (by decide)
def valeur323 : ℕ := 0x405101440510144051014405101440510144051014405101440510144051014405101440510144051014405101400000000003fff0000000fffc000fffc000fffc00000000000003ffffffc000fffc000fffffff0003ffffffffff
def valeur324 : ℕ := 0x1600580160058016005801600580160058016005801600580160058016005801600580160058016005801600580000000fffc0000003fff0003fff0000000fffffff0000000fffc000fffffff0003fff0003ffffffc000fffc000
def valeur325 : ℕ := 0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def valeur326 : ℕ := 0x15805601580560158056015805601580560158056015805601580560158056015805601580560158056015805600003fff0000000fffc0000003ffffffffff0000000fffc000fffffff00000000003ffffffc0000000000fffffff
def valeur327 : ℕ := 0x8602180860218086021808602180860218086021808602180860218086021808602180860218086021808602180fffc0000000000ffffffffffc00000000000000000fffffff000000000000000003fffffffffffffffff0000000
def valeur328 : ℕ := 0x11804601180460118046011804601180460118046011804601180460118046011804601180460118046011804600ffffffffffffff0000000000000000000000000000ffffffffffffffffffffffffc000000000000000000000000
def valeur329 : ℕ := 0x3e007801e007801e007801e007801e007801e007801e007801e007801e007801e007801e007801e007801e007801ffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000
def etat398 : List ℕ := [valeur323,valeur324,valeur325,valeur326,valeur327,valeur328,valeur329]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne488 : Ban 365 9 etat398 := viaCut proj487 borne486 (by decide +kernel) (by decide +kernel) (by decide +kernel)

def neuf : List Gate := [⟨.or,[4,5]⟩,⟨.or,[0,1]⟩,⟨.and,[7,8]⟩,⟨.and,[4,5]⟩,⟨.and,[0,3]⟩,⟨.or,[1,2]⟩,⟨.or,[12,3]⟩,⟨.and,[13,6]⟩,⟨.or,[9,10]⟩,⟨.or,[11,14]⟩,⟨.or,[15,16]⟩]
theorem neuf_ok : ∀ g ∈ neuf, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [neuf,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with h|h|h|h|h|h|h|h|h|h|h <;> subst g <;> simp
theorem neuf_calc : ∀ x : Fin 7 → Bool, Circuit.eval ⟨neuf,17⟩ (List.ofFn x) = graph x := by decide +kernel

theorem lt_count {gs : List Gate} (h : ∃ g ∈ gs, g.op = .not) : gs.countP counted < gs.length := by
  apply Nat.lt_of_le_of_ne List.countP_le_length
  intro eq
  obtain ⟨g,hg,hop⟩ := h
  have bad := List.countP_eq_length.mp eq g hg
  simp [counted,hop] at bad

end PEqualNP.Outside.L_meta_11201

open PEqualNP.Outside.L_meta_11201 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_11201 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o hfan _ he
  by_cases hn : ∃ g ∈ gs, g.op = .not
  · have fan : FanInTwo ⟨gs,o⟩ := fun g hg => ⟨(hfan g hg).1,(hfan g hg).2⟩
    obtain ⟨k,kle,live⟩ := trace ⟨gs,o⟩ fan (funext he)
    have huit : 10 ≤ k := by
      by_contra! small
      exact borne488 k (by omega) live
    have less := lt_count hn
    change k ≤ gs.countP counted at kle
    exact ⟨neuf,17,neuf_ok,by change 11 ≤ gs.length; omega,neuf_calc⟩
  · refine ⟨gs,o,?_,le_rfl,he⟩
    intro g hg
    exact ⟨(hfan g hg).1.imp_right (fun h => h.resolve_right (fun e => hn ⟨g,hg,e⟩)),(hfan g hg).2⟩
