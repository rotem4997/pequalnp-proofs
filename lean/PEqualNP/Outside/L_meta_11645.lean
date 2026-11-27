import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_11645


namespace M10720

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

end M10720



namespace M10720

def pinch (m mask i w : ℕ) : ℕ :=
  let absent := (2^m-1) ^^^ mask
  (w &&& (mask ||| (mask <<< m))) |||
    (if w.testBit i then absent else 0) |||
    (if w.testBit (m+i) then absent <<< m else 0)

private theorem pinchBits (m mask i w j : ℕ) (hm : mask < 2^m) :
    (pinch m mask i w).testBit j =
      if j < m then w.testBit (if mask.testBit j then j else i)
      else if j < m+m then w.testBit (if mask.testBit (j-m) then j else m+i)
      else false := by
  have off (k : ℕ) (hk : m ≤ k) : mask.testBit k = false :=
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) hk))
  by_cases lo : j < m
  · have n := Nat.not_le_of_lt lo
    cases h₁ : w.testBit i <;> cases h₂ : w.testBit (m+i) <;> cases h₃ : mask.testBit j <;>
      simp [pinch, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_or,
        Nat.testBit_two_pow_sub_one, Nat.testBit_shiftLeft, lo, n, h₁, h₂, h₃]
  have mj : m ≤ j := by omega
  by_cases mid : j < m+m
  · have sub : j-m < m := by omega
    cases h₁ : w.testBit i <;> cases h₂ : w.testBit (m+i) <;> cases h₃ : mask.testBit (j-m) <;>
      simp [pinch, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_or,
        Nat.testBit_two_pow_sub_one, Nat.testBit_shiftLeft, lo, mj, off _ mj, mid, sub, h₁, h₂, h₃]
  · have sub : m ≤ j-m := by omega
    cases h₁ : w.testBit i <;> cases h₂ : w.testBit (m+i) <;>
      simp [pinch, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_or,
        Nat.testBit_two_pow_sub_one, Nat.testBit_shiftLeft, lo, mj, off _ mj, mid,
        Nat.not_lt_of_ge sub, off _ sub, h₁, h₂]

def pinchProj (m mask i : ℕ) (hm : mask < 2^m) (hi : i < m) : Projection m m := by
  refine ⟨pinch m mask i, by simp [pinch], ?_, ?_, by omega⟩
  · intro d a b hd
    apply Nat.eq_of_testBit_eq
    intro j
    interval_cases d <;>
      simp only [combine, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, pinchBits _ _ _ _ _ hm] <;>
      split <;> split <;> simp [*]
  · intro a ha j hj
    have big : ¬ m+j < m := by omega
    have small : m+j < m+m := by omega
    cases h : mask.testBit j <;>
      simp [pinchBits _ _ _ _ _ hm, hj, big, small, h, ha i hi, ha j hj]

def extraTest (av : List ℕ) : List ℕ → Bool
  | [] => true
  | z::zs =>
    (av.any (fun a => av.any (fun b => (List.range 4).any (fun d => combine d a b == z)))) &&
      extraTest (av++[z]) zs

def cutTest (f t : ℕ) (p : ℕ → ℕ) (av v extra : List ℕ) : Bool :=
  let w := v.map p
  decide (f+extra.length ≤ t+w.count 0) &&
    w.all (fun x => x == 0 || (av++extra).contains x) && extraTest av extra

private theorem extraTest_pull {m k : ℕ} (av extra : List ℕ) (ok : extraTest av extra = true)
    (run : Possible m k (av++extra)) : Possible m (k+extra.length) av := by
  induction extra generalizing av with
  | nil => simpa using run
  | cons z zs ih =>
    simp only [extraTest, Bool.and_eq_true, List.any_eq_true, List.mem_range, beq_iff_eq] at ok
    obtain ⟨⟨a, ha, b, hb, d, hd, rfl⟩, tail⟩ := ok
    have prev := ih (av++[combine d a b]) tail (by simpa using run)
    obtain ⟨l, S, lim, live, sub⟩ := pullPaid hd ha hb prev
    refine ⟨l, S, ?_, live, sub⟩
    have one : (charge av (combine d a b)).toNat ≤ 1 := by cases charge av (combine d a b) <;> decide
    simp only [List.length_cons]; omega

theorem cutTest_ok {m h f t : ℕ} (p : Projection m h) {av v extra : List ℕ}
    (hw : Wide h t av) (nd : v.Nodup) (hc : cutTest f t p.toFun av v extra = true) : Ban m f v := by
  simp only [cutTest, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at hc
  obtain ⟨⟨cost, mem⟩, cert⟩ := hc
  intro k lim run
  obtain ⟨j,T,c,ok,incl⟩ := projectLive p run
  have fixed : dead p.toFun v.toFinset=(v.map p.toFun).count 0 := by
    dsimp [dead]
    have E : v.toFinset.filter (fun x => p.toFun x=0) = (v.filter (fun x => decide (p.toFun x=0))).toFinset := by ext x; simp
    rw [E,List.toFinset_card_of_nodup (nd.filter _)]
    simp only [List.count_eq_countP,List.countP_map]
    rw [List.countP_eq_length_filter]; congr 2
  rw [fixed] at c
  have bound : Possible h j (av++extra) := by
    refine ⟨j,T,le_rfl,ok,?_⟩
    intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp (incl _ hx)
    have found := mem _ (List.mem_map.mpr ⟨y,List.mem_toFinset.mp hy,rfl⟩)
    exact found.resolve_left (liveNonzero ok _ hx)
  obtain ⟨l,S,le,live,sub⟩ := extraTest_pull av extra cert bound
  exact hw ⟨l,S,by omega,live,sub⟩

end M10720

namespace Travail11645
open M10720
def cinqBase : List ℕ := [0x4290a4290a4290a0000000000fffff,0xb02c0b02c0b02c003ff003ff00000,0x8c2308c2308c23000000ffc00003ff,0x100401004010040ffc00fffffffc00,0xe0380e0380e0380fffff0000000000]
def septBase : List ℕ := [0x10a4290a4290a4280000000000fffff,0x82c0b02c0b02c0b2003ff003ff00000,0x1000000000000000,0x2308c2308c2308c000000ffc00003ff,0x2000000000000000,0x401004010040100ffc00fffffffc00,0x780e0380e0380e01fffff0000000000]
def posBits : ℕ := 0x944c183060c183060c182142850a142850a14250a142850a142850a11224489122448912242850a142850a1428448912244891224489
def negBits : ℕ := 0x140910602014201820202441808050806080809106020142018202024418080508060808091060201420182020244180805080608080
end Travail11645

namespace Travail11645
open M10720
def w0 : ℕ := 0xb02c0b02c0b02c003ff003ff00000

def w1 : ℕ := 0x100401004010040ffc00fffffffc00

def w2 : ℕ := 0x4290a4290a4290a0000000000fffff

def w3 : ℕ := 0x8c2308c2308c23000000ffc00003ff

def w4 : ℕ := 0xe0380e0380e0380fffff0000000000

def v0 : List ℕ := [w0,w1,w2,w3,w4]

def w5 : ℕ := 0x3ff

def v1 : List ℕ := [w5,w0,w1,w2,w3,w4]

def w6 : ℕ := 0x10040000400000cebffffffffffff

def w7 : ℕ := 0x100400004000000fff3affffffffff

def w8 : ℕ := 0x200800008000000314c50000000000

def v2 : List ℕ := [w6,w7,w8]

theorem h2 : Ban 60 3 v2 := viaSmall (by decide +kernel) (by decide)

def p98 : Projection 60 60 := pinchProj 60 0x314c5000c500000 20 (by decide) (by decide)

theorem minorant98 : Wide 60 3 v2 := widen (by decide +kernel) h2

theorem h1 : Ban 60 6 v1 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def w9 : ℕ := 0xffc00

def v3 : List ℕ := [w9,w0,w1,w2,w3,w4]

theorem h3 : Ban 60 6 v3 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def w10 : ℕ := 0x3ff00000

def v4 : List ℕ := [w10,w0,w1,w2,w3,w4]

def w11 : ℕ := 0x80000802fffffeb3fffffff

def w12 : ℕ := 0x400004010ffffffffffeb3ff

def w13 : ℕ := 0x10000100400000014c0014c00

def v5 : List ℕ := [w11,w12,w13]

theorem h5 : Ban 60 3 v5 := viaSmall (by decide +kernel) (by decide)

def p41 : Projection 60 60 := pinchProj 60 0x14c0014c53 0 (by decide) (by decide)

theorem minorant41 : Wide 60 3 v5 := widen (by decide +kernel) h5

theorem h4 : Ban 60 6 v4 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w14 : ℕ := 0xffc0000000

def v6 : List ℕ := [w14,w0,w1,w2,w3,w4]

theorem h6 : Ban 60 6 v6 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def w15 : ℕ := 0x3ff0000000000

def v7 : List ℕ := [w15,w0,w1,w2,w3,w4]

theorem h7 : Ban 60 6 v7 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w16 : ℕ := 0xffc000000000000

def v8 : List ℕ := [w16,w0,w1,w2,w3,w4]

theorem h8 : Ban 60 6 v8 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w17 : ℕ := 0x20080200802008000000000000000

def v9 : List ℕ := [w17,w0,w1,w2,w3,w4]

theorem h9 : Ban 60 6 v9 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w18 : ℕ := 0x280a0280a0280a0000000000fffff

def v10 : List ℕ := [w18,w0,w1,w2,w3,w4]

theorem h10 : Ban 60 6 v10 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v11 : List ℕ := [w18,w0,w1,w3,w4]

def v12 : List ℕ := [w5,w18,w0,w1,w3,w4]

theorem h12 : Ban 60 5 v12 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v13 : List ℕ := [w9,w18,w0,w1,w3,w4]

theorem h13 : Ban 60 5 v13 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v14 : List ℕ := [w10,w18,w0,w1,w3,w4]

theorem h14 : Ban 60 5 v14 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v15 : List ℕ := [w14,w18,w0,w1,w3,w4]

theorem h15 : Ban 60 5 v15 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v16 : List ℕ := [w15,w18,w0,w1,w3,w4]

theorem h16 : Ban 60 5 v16 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v17 : List ℕ := [w16,w18,w0,w1,w3,w4]

theorem h17 : Ban 60 5 v17 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w19 : ℕ := 0x80200802008020000000000fffff

def v18 : List ℕ := [w19,w18,w0,w1,w3,w4]

theorem h18 : Ban 60 5 v18 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v19 : List ℕ := [w19,w0,w1,w3,w4]

theorem h19 : Ban 60 5 v19 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v20 : List ℕ := [w17,w18,w0,w1,w3,w4]

theorem h20 : Ban 60 5 v20 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w20 : ℕ := 0x280a0280a0280a0000000000003ff

def v21 : List ℕ := [w20,w18,w0,w1,w3,w4]

theorem h21 : Ban 60 5 v21 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def w21 : ℕ := 0x280a0280a0280a0000000000ffc00

def v22 : List ℕ := [w21,w18,w0,w1,w3,w4]

theorem h22 : Ban 60 5 v22 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def w22 : ℕ := 0x300c0300c0300c003ff003ff00000

def v23 : List ℕ := [w18,w22,w0,w1,w3,w4]

theorem h23 : Ban 60 5 v23 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v24 : List ℕ := [w18,w22,w1,w3,w4]

theorem h24 : Ban 60 5 v24 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w23 : ℕ := 0x80200802008020000000000000000

def v25 : List ℕ := [w18,w23,w0,w1,w3,w4]

theorem h25 : Ban 60 5 v25 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w24 : ℕ := 0x90240902409024003ff003ff00000

def v26 : List ℕ := [w18,w24,w0,w1,w3,w4]

theorem h26 : Ban 60 5 v26 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v27 : List ℕ := [w18,w24,w1,w3,w4]

theorem h27 : Ban 60 5 v27 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w25 : ℕ := 0xb02c0b02c0b02c00000003ff00000

def v28 : List ℕ := [w18,w25,w0,w1,w3,w4]

theorem h28 : Ban 60 5 v28 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w26 : ℕ := 0xb02c0b02c0b02c003ff0000000000

def v29 : List ℕ := [w18,w26,w0,w1,w3,w4]

theorem h29 : Ban 60 5 v29 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w27 : ℕ := 0xb82e0b82e0b82e003ff003fffffff

def v30 : List ℕ := [w18,w0,w27,w1,w3,w4]

theorem h30 : Ban 60 5 v30 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w28 : ℕ := 0xc0300c0300c03000000ffc00003ff

def v31 : List ℕ := [w18,w0,w28,w1,w3,w4]

theorem h31 : Ban 60 5 v31 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v32 : List ℕ := [w18,w0,w28,w1,w4]

theorem h32 : Ban 60 5 v32 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w29 : ℕ := 0x10040100401004000000fffffffc00

def v33 : List ℕ := [w18,w0,w29,w1,w3,w4]

theorem h33 : Ban 60 5 v33 := viaSmall (by decide +kernel) (by decide)

def w30 : ℕ := 0x100401004010040ffc00003ffffc00

def v34 : List ℕ := [w18,w0,w30,w1,w3,w4]

theorem h34 : Ban 60 5 v34 := viaSmall (by decide +kernel) (by decide)

def w31 : ℕ := 0x100401004010040ffc00ffc00ffc00

def v35 : List ℕ := [w18,w0,w31,w1,w3,w4]

theorem h35 : Ban 60 5 v35 := viaSmall (by decide +kernel) (by decide)

def w32 : ℕ := 0x100401004010040ffc00fffff00000

def v36 : List ℕ := [w18,w0,w32,w1,w3,w4]

theorem h36 : Ban 60 5 v36 := viaSmall (by decide +kernel) (by decide)

def w33 : ℕ := 0x1284a1284a1284affc00ffffffffff

def v37 : List ℕ := [w18,w0,w1,w33,w3,w4]

theorem h37 : Ban 60 5 v37 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def w34 : ℕ := 0x1b06c1b06c1b06cffffffffffffc00

def v38 : List ℕ := [w18,w0,w1,w34,w3,w4]

theorem h38 : Ban 60 5 v38 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w35 : ℕ := 0x601806018060180fffff0000000000

def v39 : List ℕ := [w18,w0,w1,w35,w3]

theorem h39 : Ban 60 5 v39 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v40 : List ℕ := [w18,w0,w1,w35,w3,w4]

theorem h40 : Ban 60 5 v40 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w36 : ℕ := 0x802008020080200000000000000000

def v41 : List ℕ := [w18,w0,w1,w36,w3,w4]

theorem h41 : Ban 60 5 v41 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w37 : ℕ := 0x84210842108421000000ffc00003ff

def v42 : List ℕ := [w18,w0,w1,w37,w3,w4]

theorem h42 : Ban 60 5 v42 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v43 : List ℕ := [w18,w0,w1,w37,w4]

theorem h43 : Ban 60 5 v43 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w38 : ℕ := 0x8c2308c2308c2300000000000003ff

def v44 : List ℕ := [w18,w0,w1,w38,w3,w4]

theorem h44 : Ban 60 5 v44 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def w39 : ℕ := 0x8c2308c2308c23000000ffc0000000

def v45 : List ℕ := [w18,w0,w1,w39,w3,w4]

theorem h45 : Ban 60 5 v45 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def w40 : ℕ := 0x8ea3a8ea3a8ea3a00000ffc00fffff

def v46 : List ℕ := [w18,w0,w1,w3,w40,w4]

theorem h46 : Ban 60 5 v46 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def w41 : ℕ := 0x8f23c8f23c8f23c003fffffff003ff

def v47 : List ℕ := [w18,w0,w1,w3,w41,w4]

theorem h47 : Ban 60 5 v47 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w42 : ℕ := 0x9c2709c2709c270ffc00ffffffffff

def v48 : List ℕ := [w18,w0,w1,w3,w42,w4]

theorem h48 : Ban 60 5 v48 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def w43 : ℕ := 0xe0380e0380e0380003ff0000000000

def v49 : List ℕ := [w18,w0,w1,w3,w43,w4]

theorem h49 : Ban 60 5 v49 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w44 : ℕ := 0xe0380e0380e0380ffc000000000000

def v50 : List ℕ := [w18,w0,w1,w3,w44,w4]

theorem h50 : Ban 60 5 v50 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w45 : ℕ := 0xe2b8ae2b8ae2b8afffff00000fffff

def v51 : List ℕ := [w18,w0,w1,w3,w4,w45]

theorem h51 : Ban 60 5 v51 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w46 : ℕ := 0xeb3aceb3aceb3acfffff003ff00000

def v52 : List ℕ := [w18,w0,w1,w3,w4,w46]

theorem h52 : Ban 60 5 v52 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w47 : ℕ := 0xec3b0ec3b0ec3b0fffffffc00003ff

def v53 : List ℕ := [w18,w0,w1,w3,w4,w47]

theorem h53 : Ban 60 5 v53 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w48 : ℕ := 0xf03c0f03c0f03c0ffffffffffffc00

def v54 : List ℕ := [w18,w0,w1,w3,w4,w48]

theorem h54 : Ban 60 5 v54 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v55 : List ℕ := [w18,w0,w1,w3,w45]

theorem h55 : Ban 60 5 v55 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v56 : List ℕ := [w18,w0,w1,w3,w47]

theorem h56 : Ban 60 5 v56 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v57 : List ℕ := [w18,w0,w1,w41,w4]

theorem h57 : Ban 60 5 v57 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v58 : List ℕ := [w18,w0,w1,w4,w47]

theorem h58 : Ban 60 5 v58 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v59 : List ℕ := [w18,w27,w1,w3,w4]

theorem h59 : Ban 60 5 v59 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v60 : List ℕ := [w18,w1,w3,w41,w4]

theorem h60 : Ban 60 5 v60 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v61 : List ℕ := [w0,w27,w1,w3,w4]

theorem h61 : Ban 60 5 v61 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v62 : List ℕ := [w0,w1,w3,w4,w45]

theorem h62 : Ban 60 5 v62 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h11 : Ban 60 6 v11 := viaBranch (ws := [v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,v31,v32,v33,v34,v35,v36,v37,v38,v39,v40,v41,v42,v43,v44,v45,v46,v47,v48,v49,v50,v51,v52,v53,v54,v55,v56,v57,v58,v59,v60,v61,v62])
  (consBan h12 (consBan h13 (consBan h14 (consBan h15 (consBan h16 (consBan h17 (consBan h18 (consBan h19 (consBan h20 (consBan h21 (consBan h22 (consBan h23 (consBan h24 (consBan h25 (consBan h26 (consBan h27 (consBan h28 (consBan h29 (consBan h30 (consBan h31 (consBan h32 (consBan h33 (consBan h34 (consBan h35 (consBan h36 (consBan h37 (consBan h38 (consBan h39 (consBan h40 (consBan h41 (consBan h42 (consBan h43 (consBan h44 (consBan h45 (consBan h46 (consBan h47 (consBan h48 (consBan h49 (consBan h50 (consBan h51 (consBan h52 (consBan h53 (consBan h54 (consBan h55 (consBan h56 (consBan h57 (consBan h58 (consBan h59 (consBan h60 (consBan h61 (consBan h62 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v63 : List ℕ := [w22,w0,w1,w2,w3,w4]

theorem h63 : Ban 60 6 v63 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v64 : List ℕ := [w22,w1,w2,w3,w4]

def v65 : List ℕ := [w5,w22,w1,w2,w3,w4]

theorem h65 : Ban 60 5 v65 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v66 : List ℕ := [w9,w22,w1,w2,w3,w4]

theorem h66 : Ban 60 5 v66 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v67 : List ℕ := [w10,w22,w1,w2,w3,w4]

theorem h67 : Ban 60 5 v67 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v68 : List ℕ := [w14,w22,w1,w2,w3,w4]

theorem h68 : Ban 60 5 v68 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v69 : List ℕ := [w15,w22,w1,w2,w3,w4]

theorem h69 : Ban 60 5 v69 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v70 : List ℕ := [w16,w22,w1,w2,w3,w4]

theorem h70 : Ban 60 5 v70 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w49 : ℕ := 0x10040100401004003ff003ff00000

def v71 : List ℕ := [w49,w22,w1,w2,w3,w4]

theorem h71 : Ban 60 5 v71 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v72 : List ℕ := [w49,w1,w2,w3,w4]

theorem h72 : Ban 60 5 v72 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v73 : List ℕ := [w17,w22,w1,w2,w3,w4]

theorem h73 : Ban 60 5 v73 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v74 : List ℕ := [w18,w22,w1,w2,w3,w4]

theorem h74 : Ban 60 5 v74 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w50 : ℕ := 0x300c0300c0300c00000003ff00000

def v75 : List ℕ := [w50,w22,w1,w2,w3,w4]

theorem h75 : Ban 60 5 v75 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w51 : ℕ := 0x300c0300c0300c003ff0000000000

def v76 : List ℕ := [w51,w22,w1,w2,w3,w4]

theorem h76 : Ban 60 5 v76 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v77 : List ℕ := [w22,w28,w1,w2,w3,w4]

theorem h77 : Ban 60 5 v77 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v78 : List ℕ := [w22,w28,w1,w2,w4]

theorem h78 : Ban 60 5 v78 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v79 : List ℕ := [w22,w29,w1,w2,w3,w4]

theorem h79 : Ban 60 5 v79 := viaSmall (by decide +kernel) (by decide)

def v80 : List ℕ := [w22,w30,w1,w2,w3,w4]

theorem h80 : Ban 60 5 v80 := viaSmall (by decide +kernel) (by decide)

def v81 : List ℕ := [w22,w31,w1,w2,w3,w4]

theorem h81 : Ban 60 5 v81 := viaSmall (by decide +kernel) (by decide)

def v82 : List ℕ := [w22,w32,w1,w2,w3,w4]

theorem h82 : Ban 60 5 v82 := viaSmall (by decide +kernel) (by decide)

def w52 : ℕ := 0x1304c1304c1304cffffffffffffc00

def v83 : List ℕ := [w22,w1,w52,w2,w3,w4]

theorem h83 : Ban 60 5 v83 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w53 : ℕ := 0x401004010040100000000000000000

def v84 : List ℕ := [w22,w1,w53,w2,w3,w4]

theorem h84 : Ban 60 5 v84 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w54 : ℕ := 0x4090240902409020000000000fffff

def v85 : List ℕ := [w22,w1,w54,w2,w3,w4]

theorem h85 : Ban 60 5 v85 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v86 : List ℕ := [w22,w1,w54,w3,w4]

theorem h86 : Ban 60 5 v86 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w55 : ℕ := 0x4290a4290a4290a0000000000003ff

def v87 : List ℕ := [w22,w1,w55,w2,w3,w4]

theorem h87 : Ban 60 5 v87 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def w56 : ℕ := 0x4290a4290a4290a0000000000ffc00

def v88 : List ℕ := [w22,w1,w56,w2,w3,w4]

theorem h88 : Ban 60 5 v88 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def w57 : ℕ := 0x4390e4390e4390e003ff003fffffff

def v89 : List ℕ := [w22,w1,w2,w57,w3,w4]

theorem h89 : Ban 60 5 v89 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w58 : ℕ := 0x5294a5294a5294affc00ffffffffff

def v90 : List ℕ := [w22,w1,w2,w58,w3,w4]

theorem h90 : Ban 60 5 v90 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v91 : List ℕ := [w22,w1,w2,w35,w3]

theorem h91 : Ban 60 5 v91 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v92 : List ℕ := [w22,w1,w2,w35,w3,w4]

theorem h92 : Ban 60 5 v92 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v93 : List ℕ := [w22,w1,w2,w36,w3,w4]

theorem h93 : Ban 60 5 v93 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v94 : List ℕ := [w22,w1,w2,w38,w3,w4]

theorem h94 : Ban 60 5 v94 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v95 : List ℕ := [w22,w1,w2,w39,w3,w4]

theorem h95 : Ban 60 5 v95 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v96 : List ℕ := [w22,w1,w2,w3,w41,w4]

theorem h96 : Ban 60 5 v96 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v97 : List ℕ := [w22,w1,w2,w3,w42,w4]

theorem h97 : Ban 60 5 v97 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def w59 : ℕ := 0xa0280a0280a0280fffff0000000000

def v98 : List ℕ := [w22,w1,w2,w3,w59]

theorem h98 : Ban 60 5 v98 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v99 : List ℕ := [w22,w1,w2,w3,w59,w4]

theorem h99 : Ban 60 5 v99 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w60 : ℕ := 0xceb3aceb3aceb3a00000ffc00fffff

def v100 : List ℕ := [w22,w1,w2,w3,w60,w4]

theorem h100 : Ban 60 5 v100 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v101 : List ℕ := [w22,w1,w2,w3,w43,w4]

theorem h101 : Ban 60 5 v101 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v102 : List ℕ := [w22,w1,w2,w3,w44,w4]

theorem h102 : Ban 60 5 v102 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v103 : List ℕ := [w22,w1,w2,w3,w4,w45]

theorem h103 : Ban 60 5 v103 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w61 : ℕ := 0xe338ce338ce338cfffff003ff00000

def v104 : List ℕ := [w22,w1,w2,w3,w4,w61]

theorem h104 : Ban 60 5 v104 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v105 : List ℕ := [w22,w1,w2,w3,w4,w47]

theorem h105 : Ban 60 5 v105 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v106 : List ℕ := [w22,w1,w2,w3,w4,w48]

theorem h106 : Ban 60 5 v106 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v107 : List ℕ := [w22,w1,w2,w3,w45]

theorem h107 : Ban 60 5 v107 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v108 : List ℕ := [w22,w1,w2,w3,w47]

theorem h108 : Ban 60 5 v108 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v109 : List ℕ := [w22,w1,w2,w41,w4]

theorem h109 : Ban 60 5 v109 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v110 : List ℕ := [w22,w1,w2,w4,w47]

theorem h110 : Ban 60 5 v110 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v111 : List ℕ := [w22,w1,w57,w3,w4]

theorem h111 : Ban 60 5 v111 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v112 : List ℕ := [w22,w1,w3,w4,w45]

theorem h112 : Ban 60 5 v112 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v113 : List ℕ := [w1,w2,w57,w3,w4]

theorem h113 : Ban 60 5 v113 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v114 : List ℕ := [w1,w2,w3,w41,w4]

theorem h114 : Ban 60 5 v114 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h64 : Ban 60 6 v64 := viaBranch (ws := [v65,v66,v67,v68,v69,v70,v71,v72,v73,v74,v24,v75,v76,v77,v78,v79,v80,v81,v82,v83,v84,v85,v86,v87,v88,v89,v90,v91,v92,v93,v94,v95,v96,v97,v98,v99,v100,v101,v102,v103,v104,v105,v106,v107,v108,v109,v110,v111,v112,v113,v114])
  (consBan h65 (consBan h66 (consBan h67 (consBan h68 (consBan h69 (consBan h70 (consBan h71 (consBan h72 (consBan h73 (consBan h74 (consBan h24 (consBan h75 (consBan h76 (consBan h77 (consBan h78 (consBan h79 (consBan h80 (consBan h81 (consBan h82 (consBan h83 (consBan h84 (consBan h85 (consBan h86 (consBan h87 (consBan h88 (consBan h89 (consBan h90 (consBan h91 (consBan h92 (consBan h93 (consBan h94 (consBan h95 (consBan h96 (consBan h97 (consBan h98 (consBan h99 (consBan h100 (consBan h101 (consBan h102 (consBan h103 (consBan h104 (consBan h105 (consBan h106 (consBan h107 (consBan h108 (consBan h109 (consBan h110 (consBan h111 (consBan h112 (consBan h113 (consBan h114 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v115 : List ℕ := [w23,w0,w1,w2,w3,w4]

theorem h115 : Ban 60 6 v115 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v116 : List ℕ := [w24,w0,w1,w2,w3,w4]

theorem h116 : Ban 60 6 v116 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v117 : List ℕ := [w24,w1,w2,w3,w4]

def v118 : List ℕ := [w5,w24,w1,w2,w3,w4]

theorem h118 : Ban 60 5 v118 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v119 : List ℕ := [w9,w24,w1,w2,w3,w4]

theorem h119 : Ban 60 5 v119 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v120 : List ℕ := [w10,w24,w1,w2,w3,w4]

theorem h120 : Ban 60 5 v120 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v121 : List ℕ := [w14,w24,w1,w2,w3,w4]

theorem h121 : Ban 60 5 v121 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v122 : List ℕ := [w15,w24,w1,w2,w3,w4]

theorem h122 : Ban 60 5 v122 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v123 : List ℕ := [w16,w24,w1,w2,w3,w4]

theorem h123 : Ban 60 5 v123 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v124 : List ℕ := [w49,w24,w1,w2,w3,w4]

theorem h124 : Ban 60 5 v124 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v125 : List ℕ := [w18,w24,w1,w2,w3,w4]

theorem h125 : Ban 60 5 v125 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v126 : List ℕ := [w23,w24,w1,w2,w3,w4]

theorem h126 : Ban 60 5 v126 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w62 : ℕ := 0x9024090240902400000003ff00000

def v127 : List ℕ := [w62,w24,w1,w2,w3,w4]

theorem h127 : Ban 60 5 v127 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w63 : ℕ := 0x90240902409024003ff0000000000

def v128 : List ℕ := [w63,w24,w1,w2,w3,w4]

theorem h128 : Ban 60 5 v128 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v129 : List ℕ := [w24,w28,w1,w2,w3,w4]

theorem h129 : Ban 60 5 v129 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v130 : List ℕ := [w24,w28,w1,w2,w4]

theorem h130 : Ban 60 5 v130 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v131 : List ℕ := [w24,w29,w1,w2,w3,w4]

theorem h131 : Ban 60 5 v131 := viaSmall (by decide +kernel) (by decide)

def v132 : List ℕ := [w24,w30,w1,w2,w3,w4]

theorem h132 : Ban 60 5 v132 := viaSmall (by decide +kernel) (by decide)

def v133 : List ℕ := [w24,w31,w1,w2,w3,w4]

theorem h133 : Ban 60 5 v133 := viaSmall (by decide +kernel) (by decide)

def v134 : List ℕ := [w24,w32,w1,w2,w3,w4]

theorem h134 : Ban 60 5 v134 := viaSmall (by decide +kernel) (by decide)

def w64 : ℕ := 0x190641906419064ffffffffffffc00

def v135 : List ℕ := [w24,w1,w64,w2,w3,w4]

theorem h135 : Ban 60 5 v135 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v136 : List ℕ := [w24,w1,w53,w2,w3,w4]

theorem h136 : Ban 60 5 v136 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v137 : List ℕ := [w24,w1,w55,w2,w3,w4]

theorem h137 : Ban 60 5 v137 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v138 : List ℕ := [w24,w1,w56,w2,w3,w4]

theorem h138 : Ban 60 5 v138 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def w65 : ℕ := 0x4b92e4b92e4b92e003ff003fffffff

def v139 : List ℕ := [w24,w1,w2,w65,w3,w4]

theorem h139 : Ban 60 5 v139 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v140 : List ℕ := [w24,w1,w2,w58,w3,w4]

theorem h140 : Ban 60 5 v140 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v141 : List ℕ := [w24,w1,w2,w35,w3]

theorem h141 : Ban 60 5 v141 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v142 : List ℕ := [w24,w1,w2,w35,w3,w4]

theorem h142 : Ban 60 5 v142 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v143 : List ℕ := [w24,w1,w2,w36,w3,w4]

theorem h143 : Ban 60 5 v143 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v144 : List ℕ := [w24,w1,w2,w37,w3,w4]

theorem h144 : Ban 60 5 v144 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v145 : List ℕ := [w24,w1,w2,w37,w4]

theorem h145 : Ban 60 5 v145 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v146 : List ℕ := [w24,w1,w2,w38,w3,w4]

theorem h146 : Ban 60 5 v146 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v147 : List ℕ := [w24,w1,w2,w39,w3,w4]

theorem h147 : Ban 60 5 v147 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def w66 : ℕ := 0x8d2348d2348d234003fffffff003ff

def v148 : List ℕ := [w24,w1,w2,w3,w66,w4]

theorem h148 : Ban 60 5 v148 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v149 : List ℕ := [w24,w1,w2,w3,w42,w4]

theorem h149 : Ban 60 5 v149 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v150 : List ℕ := [w24,w1,w2,w3,w59]

theorem h150 : Ban 60 5 v150 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v151 : List ℕ := [w24,w1,w2,w3,w59,w4]

theorem h151 : Ban 60 5 v151 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v152 : List ℕ := [w24,w1,w2,w3,w60,w4]

theorem h152 : Ban 60 5 v152 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v153 : List ℕ := [w24,w1,w2,w3,w43,w4]

theorem h153 : Ban 60 5 v153 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v154 : List ℕ := [w24,w1,w2,w3,w44,w4]

theorem h154 : Ban 60 5 v154 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v155 : List ℕ := [w24,w1,w2,w3,w4,w45]

theorem h155 : Ban 60 5 v155 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w67 : ℕ := 0xe93a4e93a4e93a4fffff003ff00000

def v156 : List ℕ := [w24,w1,w2,w3,w4,w67]

theorem h156 : Ban 60 5 v156 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v157 : List ℕ := [w24,w1,w2,w3,w4,w47]

theorem h157 : Ban 60 5 v157 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v158 : List ℕ := [w24,w1,w2,w3,w4,w48]

theorem h158 : Ban 60 5 v158 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v159 : List ℕ := [w24,w1,w2,w3,w45]

theorem h159 : Ban 60 5 v159 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v160 : List ℕ := [w24,w1,w2,w3,w47]

theorem h160 : Ban 60 5 v160 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v161 : List ℕ := [w24,w1,w2,w66,w4]

theorem h161 : Ban 60 5 v161 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v162 : List ℕ := [w24,w1,w2,w4,w47]

theorem h162 : Ban 60 5 v162 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v163 : List ℕ := [w24,w1,w65,w3,w4]

theorem h163 : Ban 60 5 v163 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v164 : List ℕ := [w24,w1,w3,w4,w45]

theorem h164 : Ban 60 5 v164 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v165 : List ℕ := [w1,w2,w65,w3,w4]

theorem h165 : Ban 60 5 v165 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v166 : List ℕ := [w1,w2,w3,w66,w4]

theorem h166 : Ban 60 5 v166 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h117 : Ban 60 6 v117 := viaBranch (ws := [v118,v119,v120,v121,v122,v123,v124,v72,v125,v27,v126,v127,v128,v129,v130,v131,v132,v133,v134,v135,v136,v137,v138,v139,v140,v141,v142,v143,v144,v145,v146,v147,v148,v149,v150,v151,v152,v153,v154,v155,v156,v157,v158,v159,v160,v161,v162,v163,v164,v165,v166])
  (consBan h118 (consBan h119 (consBan h120 (consBan h121 (consBan h122 (consBan h123 (consBan h124 (consBan h72 (consBan h125 (consBan h27 (consBan h126 (consBan h127 (consBan h128 (consBan h129 (consBan h130 (consBan h131 (consBan h132 (consBan h133 (consBan h134 (consBan h135 (consBan h136 (consBan h137 (consBan h138 (consBan h139 (consBan h140 (consBan h141 (consBan h142 (consBan h143 (consBan h144 (consBan h145 (consBan h146 (consBan h147 (consBan h148 (consBan h149 (consBan h150 (consBan h151 (consBan h152 (consBan h153 (consBan h154 (consBan h155 (consBan h156 (consBan h157 (consBan h158 (consBan h159 (consBan h160 (consBan h161 (consBan h162 (consBan h163 (consBan h164 (consBan h165 (consBan h166 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v167 : List ℕ := [w25,w0,w1,w2,w3,w4]

theorem h167 : Ban 60 6 v167 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v168 : List ℕ := [w26,w0,w1,w2,w3,w4]

theorem h168 : Ban 60 6 v168 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v169 : List ℕ := [w0,w28,w1,w2,w3,w4]

theorem h169 : Ban 60 6 v169 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v170 : List ℕ := [w0,w28,w1,w2,w4]

def v171 : List ℕ := [w5,w0,w28,w1,w2,w4]

theorem h171 : Ban 60 5 v171 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v172 : List ℕ := [w9,w0,w28,w1,w2,w4]

theorem h172 : Ban 60 5 v172 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v173 : List ℕ := [w10,w0,w28,w1,w2,w4]

theorem h173 : Ban 60 5 v173 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v174 : List ℕ := [w14,w0,w28,w1,w2,w4]

theorem h174 : Ban 60 5 v174 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v175 : List ℕ := [w15,w0,w28,w1,w2,w4]

theorem h175 : Ban 60 5 v175 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v176 : List ℕ := [w16,w0,w28,w1,w2,w4]

theorem h176 : Ban 60 5 v176 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v177 : List ℕ := [w17,w0,w28,w1,w2,w4]

theorem h177 : Ban 60 5 v177 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v178 : List ℕ := [w18,w0,w28,w1,w2,w4]

theorem h178 : Ban 60 5 v178 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v179 : List ℕ := [w22,w0,w28,w1,w2,w4]

theorem h179 : Ban 60 5 v179 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w68 : ℕ := 0x4010040100401000000ffc00003ff

def v180 : List ℕ := [w68,w0,w28,w1,w2,w4]

theorem h180 : Ban 60 5 v180 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v181 : List ℕ := [w68,w0,w1,w2,w4]

theorem h181 : Ban 60 5 v181 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v182 : List ℕ := [w23,w0,w28,w1,w2,w4]

theorem h182 : Ban 60 5 v182 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v183 : List ℕ := [w24,w0,w28,w1,w2,w4]

theorem h183 : Ban 60 5 v183 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v184 : List ℕ := [w25,w0,w28,w1,w2,w4]

theorem h184 : Ban 60 5 v184 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v185 : List ℕ := [w26,w0,w28,w1,w2,w4]

theorem h185 : Ban 60 5 v185 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w69 : ℕ := 0xc0300c0300c0300000000000003ff

def v186 : List ℕ := [w0,w69,w28,w1,w2,w4]

theorem h186 : Ban 60 5 v186 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def w70 : ℕ := 0xc0300c0300c03000000ffc0000000

def v187 : List ℕ := [w0,w70,w28,w1,w2,w4]

theorem h187 : Ban 60 5 v187 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def w71 : ℕ := 0xf03c0f03c0f03c003fffffff003ff

def v188 : List ℕ := [w0,w28,w71,w1,w2,w4]

theorem h188 : Ban 60 5 v188 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v189 : List ℕ := [w0,w28,w29,w1,w2,w4]

theorem h189 : Ban 60 5 v189 := viaSmall (by decide +kernel) (by decide)

def v190 : List ℕ := [w0,w28,w30,w1,w2,w4]

theorem h190 : Ban 60 5 v190 := viaSmall (by decide +kernel) (by decide)

def v191 : List ℕ := [w0,w28,w31,w1,w2,w4]

theorem h191 : Ban 60 5 v191 := viaSmall (by decide +kernel) (by decide)

def v192 : List ℕ := [w0,w28,w32,w1,w2,w4]

theorem h192 : Ban 60 5 v192 := viaSmall (by decide +kernel) (by decide)

def v193 : List ℕ := [w0,w28,w1,w34,w2,w4]

theorem h193 : Ban 60 5 v193 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w72 : ℕ := 0x1c0701c0701c070ffc00ffffffffff

def v194 : List ℕ := [w0,w28,w1,w72,w2,w4]

theorem h194 : Ban 60 5 v194 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v195 : List ℕ := [w0,w28,w1,w53,w2,w4]

theorem h195 : Ban 60 5 v195 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v196 : List ℕ := [w0,w28,w1,w54,w2,w4]

theorem h196 : Ban 60 5 v196 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v197 : List ℕ := [w0,w28,w1,w54,w4]

theorem h197 : Ban 60 5 v197 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v198 : List ℕ := [w0,w28,w1,w55,w2,w4]

theorem h198 : Ban 60 5 v198 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v199 : List ℕ := [w0,w28,w1,w56,w2,w4]

theorem h199 : Ban 60 5 v199 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v200 : List ℕ := [w0,w28,w1,w2,w65,w4]

theorem h200 : Ban 60 5 v200 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w73 : ℕ := 0x4e93a4e93a4e93a00000ffc00fffff

def v201 : List ℕ := [w0,w28,w1,w2,w73,w4]

theorem h201 : Ban 60 5 v201 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v202 : List ℕ := [w0,w28,w1,w2,w58,w4]

theorem h202 : Ban 60 5 v202 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v203 : List ℕ := [w0,w28,w1,w2,w59]

theorem h203 : Ban 60 5 v203 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v204 : List ℕ := [w0,w28,w1,w2,w59,w4]

theorem h204 : Ban 60 5 v204 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v205 : List ℕ := [w0,w28,w1,w2,w43,w4]

theorem h205 : Ban 60 5 v205 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v206 : List ℕ := [w0,w28,w1,w2,w44,w4]

theorem h206 : Ban 60 5 v206 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v207 : List ℕ := [w0,w28,w1,w2,w4,w45]

theorem h207 : Ban 60 5 v207 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v208 : List ℕ := [w0,w28,w1,w2,w4,w46]

theorem h208 : Ban 60 5 v208 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v209 : List ℕ := [w0,w28,w1,w2,w4,w47]

theorem h209 : Ban 60 5 v209 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v210 : List ℕ := [w0,w28,w1,w2,w4,w48]

theorem h210 : Ban 60 5 v210 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v211 : List ℕ := [w0,w28,w1,w2,w45]

theorem h211 : Ban 60 5 v211 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v212 : List ℕ := [w0,w28,w1,w2,w47]

theorem h212 : Ban 60 5 v212 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v213 : List ℕ := [w0,w28,w1,w65,w4]

theorem h213 : Ban 60 5 v213 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v214 : List ℕ := [w0,w28,w1,w4,w45]

theorem h214 : Ban 60 5 v214 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v215 : List ℕ := [w0,w71,w1,w2,w4]

theorem h215 : Ban 60 5 v215 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v216 : List ℕ := [w0,w1,w2,w4,w47]

theorem h216 : Ban 60 5 v216 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v217 : List ℕ := [w28,w71,w1,w2,w4]

theorem h217 : Ban 60 5 v217 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v218 : List ℕ := [w28,w1,w2,w65,w4]

theorem h218 : Ban 60 5 v218 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h170 : Ban 60 6 v170 := viaBranch (ws := [v171,v172,v173,v174,v175,v176,v177,v178,v32,v179,v78,v180,v181,v182,v183,v130,v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218])
  (consBan h171 (consBan h172 (consBan h173 (consBan h174 (consBan h175 (consBan h176 (consBan h177 (consBan h178 (consBan h32 (consBan h179 (consBan h78 (consBan h180 (consBan h181 (consBan h182 (consBan h183 (consBan h130 (consBan h184 (consBan h185 (consBan h186 (consBan h187 (consBan h188 (consBan h189 (consBan h190 (consBan h191 (consBan h192 (consBan h193 (consBan h194 (consBan h195 (consBan h196 (consBan h197 (consBan h198 (consBan h199 (consBan h200 (consBan h201 (consBan h202 (consBan h203 (consBan h204 (consBan h205 (consBan h206 (consBan h207 (consBan h208 (consBan h209 (consBan h210 (consBan h211 (consBan h212 (consBan h213 (consBan h214 (consBan h215 (consBan h216 (consBan h217 (consBan h218 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v219 : List ℕ := [w0,w29,w1,w2,w3,w4]

theorem h220 : Ban 60 5 v3 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

theorem h221 : Ban 60 5 v4 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

theorem h222 : Ban 60 5 v6 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v220 : List ℕ := [w15,w0,w29,w1,w2,w3]

theorem h223 : Ban 60 5 v220 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v221 : List ℕ := [w16,w0,w29,w2,w3,w4]

theorem h224 : Ban 60 5 v221 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

theorem h225 : Ban 60 5 v8 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v222 : List ℕ := [w25,w0,w29,w1,w2,w3]

theorem h226 : Ban 60 5 v222 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

theorem h227 : Ban 60 5 v168 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w74 : ℕ := 0x10040100401004000000003ffffc00

def v223 : List ℕ := [w0,w74,w1,w2,w3,w4]

theorem h228 : Ban 60 5 v223 := viaSmall (by decide +kernel) (by decide)

def w75 : ℕ := 0x10040100401004000000ffc00ffc00

def v224 : List ℕ := [w0,w75,w1,w2,w3,w4]

theorem h229 : Ban 60 5 v224 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w76 : ℕ := 0x10040100401004000000fffff00000

def v225 : List ℕ := [w0,w76,w1,w2,w3,w4]

theorem h230 : Ban 60 5 v225 := viaSmall (by decide +kernel) (by decide)

def v226 : List ℕ := [w0,w29,w30,w2,w3,w4]

theorem h231 : Ban 60 5 v226 := viaSmall (by decide +kernel) (by decide)

def v227 : List ℕ := [w0,w29,w31,w2,w3,w4]

theorem h232 : Ban 60 5 v227 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v228 : List ℕ := [w0,w29,w32,w2,w3,w4]

theorem h233 : Ban 60 5 v228 := viaSmall (by decide +kernel) (by decide)

def v229 : List ℕ := [w0,w29,w1,w54,w3,w4]

theorem h234 : Ban 60 5 v229 := viaSmall (by decide +kernel) (by decide)

def v230 : List ℕ := [w0,w29,w1,w2,w35,w3]

theorem h235 : Ban 60 5 v230 := viaSmall (by decide +kernel) (by decide)

def v231 : List ℕ := [w0,w29,w1,w2,w37,w4]

theorem h236 : Ban 60 5 v231 := viaSmall (by decide +kernel) (by decide)

def v232 : List ℕ := [w0,w29,w1,w2,w3,w59]

theorem h237 : Ban 60 5 v232 := viaSmall (by decide +kernel) (by decide)

def v233 : List ℕ := [w0,w29,w1,w2,w3,w43]

theorem h238 : Ban 60 5 v233 := viaSmall (by decide +kernel) (by decide)

def v234 : List ℕ := [w0,w29,w1,w2,w3,w45]

theorem h239 : Ban 60 5 v234 := viaSmall (by decide +kernel) (by decide)

def v235 : List ℕ := [w0,w29,w1,w2,w3,w47]

theorem h240 : Ban 60 5 v235 := viaSmall (by decide +kernel) (by decide)

def v236 : List ℕ := [w0,w29,w1,w2,w3,w48]

theorem h241 : Ban 60 5 v236 := viaSmall (by decide +kernel) (by decide)

def v237 : List ℕ := [w0,w29,w1,w2,w41,w4]

theorem h242 : Ban 60 5 v237 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v238 : List ℕ := [w0,w29,w1,w2,w4,w47]

theorem h243 : Ban 60 5 v238 := viaSmall (by decide +kernel) (by decide)

def v239 : List ℕ := [w0,w29,w1,w65,w3,w4]

theorem h244 : Ban 60 5 v239 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v240 : List ℕ := [w0,w29,w1,w3,w4,w45]

theorem h245 : Ban 60 5 v240 := viaSmall (by decide +kernel) (by decide)

def v241 : List ℕ := [w0,w29,w34,w2,w3,w4]

theorem h246 : Ban 60 5 v241 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v242 : List ℕ := [w0,w29,w2,w58,w3,w4]

theorem h247 : Ban 60 5 v242 := viaSmall (by decide +kernel) (by decide)

def v243 : List ℕ := [w0,w29,w2,w3,w42,w4]

theorem h248 : Ban 60 5 v243 := viaSmall (by decide +kernel) (by decide)

def v244 : List ℕ := [w0,w29,w2,w3,w43,w4]

theorem h249 : Ban 60 5 v244 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w77 : ℕ := 0x1b06c1b06c1b06c003fffffffffc00

def v245 : List ℕ := [w0,w1,w77,w2,w3,w4]

theorem h250 : Ban 60 5 v245 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v246 : List ℕ := [w0,w1,w55,w2,w3,w4]

theorem h251 : Ban 60 5 v246 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def w78 : ℕ := 0x5294a5294a5294a00000ffffffffff

def v247 : List ℕ := [w0,w1,w2,w78,w3,w4]

theorem h252 : Ban 60 5 v247 := viaSmall (by decide +kernel) (by decide)

def v248 : List ℕ := [w0,w1,w2,w38,w3,w4]

theorem h253 : Ban 60 5 v248 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def w79 : ℕ := 0x9c2709c2709c27000000ffffffffff

def v249 : List ℕ := [w0,w1,w2,w3,w79,w4]

theorem h254 : Ban 60 5 v249 := viaSmall (by decide +kernel) (by decide)

def v250 : List ℕ := [w0,w1,w2,w3,w4,w48]

theorem h255 : Ban 60 5 v250 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v251 : List ℕ := [w29,w1,w2,w65,w3,w4]

theorem h256 : Ban 60 5 v251 := viaSmall (by decide +kernel) (by decide)

def v252 : List ℕ := [w29,w1,w2,w3,w41,w4]

theorem h257 : Ban 60 5 v252 := viaSmall (by decide +kernel) (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h219 : Ban 60 6 v219 := viaBranch (ws := [v3,v4,v6,v220,v221,v8,v33,v79,v131,v222,v168,v189,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232,v233,v234,v235,v236,v237,v238,v239,v240,v241,v242,v243,v244,v245,v246,v247,v248,v249,v250,v251,v252])
  (consBan h220 (consBan h221 (consBan h222 (consBan h223 (consBan h224 (consBan h225 (consBan h33 (consBan h79 (consBan h131 (consBan h226 (consBan h227 (consBan h189 (consBan h228 (consBan h229 (consBan h230 (consBan h231 (consBan h232 (consBan h233 (consBan h234 (consBan h235 (consBan h236 (consBan h237 (consBan h238 (consBan h239 (consBan h240 (consBan h241 (consBan h242 (consBan h243 (consBan h244 (consBan h245 (consBan h246 (consBan h247 (consBan h248 (consBan h249 (consBan h250 (consBan h251 (consBan h252 (consBan h253 (consBan h254 (consBan h255 (consBan h256 (consBan h257 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v253 : List ℕ := [w0,w30,w1,w2,w3,w4]

def v254 : List ℕ := [w5,w0,w30,w1,w2,w4]

theorem h259 : Ban 60 5 v254 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v255 : List ℕ := [w14,w0,w30,w2,w3,w4]

theorem h260 : Ban 60 5 v255 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def w80 : ℕ := 0x100401004010040ffc0000000ffc00

def v256 : List ℕ := [w0,w80,w1,w2,w3,w4]

theorem h261 : Ban 60 5 v256 := viaSmall (by decide +kernel) (by decide)

def w81 : ℕ := 0x100401004010040ffc00003ff00000

def v257 : List ℕ := [w0,w81,w1,w2,w3,w4]

theorem h262 : Ban 60 5 v257 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v258 : List ℕ := [w0,w30,w31,w2,w3,w4]

theorem h263 : Ban 60 5 v258 := viaSmall (by decide +kernel) (by decide)

def v259 : List ℕ := [w0,w30,w32,w2,w3,w4]

theorem h264 : Ban 60 5 v259 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v260 : List ℕ := [w0,w30,w1,w54,w3,w4]

theorem h265 : Ban 60 5 v260 := viaSmall (by decide +kernel) (by decide)

def v261 : List ℕ := [w0,w30,w1,w56,w2,w4]

theorem h266 : Ban 60 5 v261 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v262 : List ℕ := [w0,w30,w1,w2,w35,w3]

theorem h267 : Ban 60 5 v262 := viaSmall (by decide +kernel) (by decide)

def v263 : List ℕ := [w0,w30,w1,w2,w37,w4]

theorem h268 : Ban 60 5 v263 := viaSmall (by decide +kernel) (by decide)

def v264 : List ℕ := [w0,w30,w1,w2,w38,w4]

theorem h269 : Ban 60 5 v264 := viaSmall (by decide +kernel) (by decide)

def v265 : List ℕ := [w0,w30,w1,w2,w3,w59]

theorem h270 : Ban 60 5 v265 := viaSmall (by decide +kernel) (by decide)

def v266 : List ℕ := [w0,w30,w1,w2,w3,w45]

theorem h271 : Ban 60 5 v266 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v267 : List ℕ := [w0,w30,w1,w2,w3,w47]

theorem h272 : Ban 60 5 v267 := viaSmall (by decide +kernel) (by decide)

def v268 : List ℕ := [w0,w30,w1,w2,w41,w4]

theorem h273 : Ban 60 5 v268 := viaSmall (by decide +kernel) (by decide)

def v269 : List ℕ := [w0,w30,w1,w2,w42,w4]

theorem h274 : Ban 60 5 v269 := viaSmall (by decide +kernel) (by decide)

def v270 : List ℕ := [w0,w30,w1,w2,w4,w47]

theorem h275 : Ban 60 5 v270 := viaSmall (by decide +kernel) (by decide)

def v271 : List ℕ := [w0,w30,w1,w65,w3,w4]

theorem h276 : Ban 60 5 v271 := viaSmall (by decide +kernel) (by decide)

def v272 : List ℕ := [w0,w30,w1,w3,w4,w45]

theorem h277 : Ban 60 5 v272 := viaSmall (by decide +kernel) (by decide)

def v273 : List ℕ := [w0,w30,w34,w2,w3,w4]

theorem h278 : Ban 60 5 v273 := viaSmall (by decide +kernel) (by decide)

def v274 : List ℕ := [w0,w30,w2,w58,w3,w4]

theorem h279 : Ban 60 5 v274 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v275 : List ℕ := [w0,w30,w2,w38,w3,w4]

theorem h280 : Ban 60 5 v275 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v276 : List ℕ := [w0,w30,w2,w3,w4,w48]

theorem h281 : Ban 60 5 v276 := viaSmall (by decide +kernel) (by decide)

def w82 : ℕ := 0x1b06c1b06c1b06cfffff003ffffc00

def v277 : List ℕ := [w0,w1,w82,w2,w3,w4]

theorem h282 : Ban 60 5 v277 := viaSmall (by decide +kernel) (by decide)

def w83 : ℕ := 0x5294a5294a5294affc00003fffffff

def v278 : List ℕ := [w0,w1,w2,w83,w3,w4]

theorem h283 : Ban 60 5 v278 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v279 : List ℕ := [w0,w1,w2,w3,w42,w4]

theorem h284 : Ban 60 5 v279 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v280 : List ℕ := [w0,w1,w2,w3,w43,w4]

theorem h285 : Ban 60 5 v280 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w84 : ℕ := 0xf03c0f03c0f03c0fffff003ffffc00

def v281 : List ℕ := [w0,w1,w2,w3,w4,w84]

theorem h286 : Ban 60 5 v281 := viaSmall (by decide +kernel) (by decide)

def v282 : List ℕ := [w30,w1,w2,w65,w3,w4]

theorem h287 : Ban 60 5 v282 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v283 : List ℕ := [w30,w1,w2,w3,w41,w4]

theorem h288 : Ban 60 5 v283 := viaSmall (by decide +kernel) (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h258 : Ban 60 6 v253 := viaBranch (ws := [v254,v3,v4,v255,v6,v8,v34,v80,v132,v168,v190,v223,v226,v256,v257,v258,v259,v260,v261,v262,v263,v264,v265,v266,v267,v268,v269,v270,v271,v272,v273,v274,v275,v276,v277,v246,v278,v279,v280,v281,v282,v283])
  (consBan h259 (consBan h220 (consBan h221 (consBan h260 (consBan h222 (consBan h225 (consBan h34 (consBan h80 (consBan h132 (consBan h227 (consBan h190 (consBan h228 (consBan h231 (consBan h261 (consBan h262 (consBan h263 (consBan h264 (consBan h265 (consBan h266 (consBan h267 (consBan h268 (consBan h269 (consBan h270 (consBan h271 (consBan h272 (consBan h273 (consBan h274 (consBan h275 (consBan h276 (consBan h277 (consBan h278 (consBan h279 (consBan h280 (consBan h281 (consBan h282 (consBan h251 (consBan h283 (consBan h284 (consBan h285 (consBan h286 (consBan h287 (consBan h288 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v284 : List ℕ := [w0,w31,w1,w2,w3,w4]

def v285 : List ℕ := [w10,w0,w31,w2,w3,w4]

theorem h290 : Ban 60 5 v285 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v286 : List ℕ := [w15,w31,w1,w2,w3,w4]

theorem h291 : Ban 60 5 v286 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v287 : List ℕ := [w26,w0,w31,w2,w3,w4]

theorem h292 : Ban 60 5 v287 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v288 : List ℕ := [w26,w31,w1,w2,w3,w4]

theorem h293 : Ban 60 5 v288 := viaSmall (by decide +kernel) (by decide)

def w85 : ℕ := 0x100401004010040ffc00ffc0000000

def v289 : List ℕ := [w0,w85,w1,w2,w3,w4]

theorem h294 : Ban 60 5 v289 := viaSmall (by decide +kernel) (by decide)

def v290 : List ℕ := [w0,w31,w32,w2,w3,w4]

theorem h295 : Ban 60 5 v290 := viaSmall (by decide +kernel) (by decide)

def v291 : List ℕ := [w0,w31,w1,w54,w3,w4]

theorem h296 : Ban 60 5 v291 := viaSmall (by decide +kernel) (by decide)

def v292 : List ℕ := [w0,w31,w1,w2,w35,w3]

theorem h297 : Ban 60 5 v292 := viaSmall (by decide +kernel) (by decide)

def v293 : List ℕ := [w0,w31,w1,w2,w37,w4]

theorem h298 : Ban 60 5 v293 := viaSmall (by decide +kernel) (by decide)

def v294 : List ℕ := [w0,w31,w1,w2,w3,w59]

theorem h299 : Ban 60 5 v294 := viaSmall (by decide +kernel) (by decide)

def v295 : List ℕ := [w0,w31,w1,w2,w3,w45]

theorem h300 : Ban 60 5 v295 := viaSmall (by decide +kernel) (by decide)

def v296 : List ℕ := [w0,w31,w1,w2,w3,w47]

theorem h301 : Ban 60 5 v296 := viaSmall (by decide +kernel) (by decide)

def v297 : List ℕ := [w0,w31,w1,w2,w41,w4]

theorem h302 : Ban 60 5 v297 := viaSmall (by decide +kernel) (by decide)

def v298 : List ℕ := [w0,w31,w1,w2,w4,w47]

theorem h303 : Ban 60 5 v298 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v299 : List ℕ := [w0,w31,w1,w65,w3,w4]

theorem h304 : Ban 60 5 v299 := viaSmall (by decide +kernel) (by decide)

def v300 : List ℕ := [w0,w31,w1,w3,w4,w45]

theorem h305 : Ban 60 5 v300 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v301 : List ℕ := [w0,w31,w2,w58,w3,w4]

theorem h306 : Ban 60 5 v301 := viaSmall (by decide +kernel) (by decide)

def v302 : List ℕ := [w0,w31,w2,w3,w42,w4]

theorem h307 : Ban 60 5 v302 := viaSmall (by decide +kernel) (by decide)

def v303 : List ℕ := [w0,w31,w2,w3,w4,w48]

theorem h308 : Ban 60 5 v303 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v304 : List ℕ := [w0,w1,w34,w2,w3,w4]

theorem h309 : Ban 60 5 v304 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w86 : ℕ := 0x5294a5294a5294affc00ffc00fffff

def v305 : List ℕ := [w0,w1,w2,w86,w3,w4]

theorem h310 : Ban 60 5 v305 := viaSmall (by decide +kernel) (by decide)

def w87 : ℕ := 0x9c2709c2709c270ffc00ffc00fffff

def v306 : List ℕ := [w0,w1,w2,w3,w87,w4]

theorem h311 : Ban 60 5 v306 := viaSmall (by decide +kernel) (by decide)

def w88 : ℕ := 0xf03c0f03c0f03c0fffffffc00ffc00

def v307 : List ℕ := [w0,w1,w2,w3,w4,w88]

theorem h312 : Ban 60 5 v307 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v308 : List ℕ := [w31,w1,w34,w2,w3,w4]

theorem h313 : Ban 60 5 v308 := viaSmall (by decide +kernel) (by decide)

def v309 : List ℕ := [w31,w1,w2,w65,w3,w4]

theorem h314 : Ban 60 5 v309 := viaSmall (by decide +kernel) (by decide)

def v310 : List ℕ := [w31,w1,w2,w3,w41,w4]

theorem h315 : Ban 60 5 v310 := viaSmall (by decide +kernel) (by decide)

def v311 : List ℕ := [w31,w1,w2,w3,w44,w4]

theorem h316 : Ban 60 5 v311 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h289 : Ban 60 6 v284 := viaBranch (ws := [v3,v285,v4,v6,v286,v8,v35,v81,v133,v287,v288,v191,v224,v227,v256,v258,v289,v290,v291,v292,v293,v294,v295,v296,v297,v298,v299,v300,v301,v302,v303,v304,v246,v305,v248,v306,v280,v307,v308,v309,v310,v311])
  (consBan h220 (consBan h290 (consBan h221 (consBan h222 (consBan h291 (consBan h225 (consBan h35 (consBan h81 (consBan h133 (consBan h292 (consBan h293 (consBan h191 (consBan h229 (consBan h232 (consBan h261 (consBan h263 (consBan h294 (consBan h295 (consBan h296 (consBan h297 (consBan h298 (consBan h299 (consBan h300 (consBan h301 (consBan h302 (consBan h303 (consBan h304 (consBan h305 (consBan h306 (consBan h307 (consBan h308 (consBan h309 (consBan h251 (consBan h310 (consBan h253 (consBan h311 (consBan h285 (consBan h312 (consBan h313 (consBan h314 (consBan h315 (consBan h316 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v312 : List ℕ := [w0,w32,w1,w2,w3,w4]

def v313 : List ℕ := [w5,w0,w32,w1,w3,w4]

theorem h318 : Ban 60 5 v313 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v314 : List ℕ := [w9,w0,w32,w2,w3,w4]

theorem h319 : Ban 60 5 v314 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v315 : List ℕ := [w0,w32,w1,w54,w3,w4]

theorem h320 : Ban 60 5 v315 := viaSmall (by decide +kernel) (by decide)

def v316 : List ℕ := [w0,w32,w1,w55,w3,w4]

theorem h321 : Ban 60 5 v316 := viaSmall (by decide +kernel) (by decide)

def v317 : List ℕ := [w0,w32,w1,w2,w35,w3]

theorem h322 : Ban 60 5 v317 := viaSmall (by decide +kernel) (by decide)

def v318 : List ℕ := [w0,w32,w1,w2,w37,w4]

theorem h323 : Ban 60 5 v318 := viaSmall (by decide +kernel) (by decide)

def v319 : List ℕ := [w0,w32,w1,w2,w3,w59]

theorem h324 : Ban 60 5 v319 := viaSmall (by decide +kernel) (by decide)

def v320 : List ℕ := [w0,w32,w1,w2,w3,w45]

theorem h325 : Ban 60 5 v320 := viaSmall (by decide +kernel) (by decide)

def v321 : List ℕ := [w0,w32,w1,w2,w3,w47]

theorem h326 : Ban 60 5 v321 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v322 : List ℕ := [w0,w32,w1,w2,w41,w4]

theorem h327 : Ban 60 5 v322 := viaSmall (by decide +kernel) (by decide)

def v323 : List ℕ := [w0,w32,w1,w2,w4,w47]

theorem h328 : Ban 60 5 v323 := viaSmall (by decide +kernel) (by decide)

def v324 : List ℕ := [w0,w32,w1,w65,w3,w4]

theorem h329 : Ban 60 5 v324 := viaSmall (by decide +kernel) (by decide)

def v325 : List ℕ := [w0,w32,w1,w58,w3,w4]

theorem h330 : Ban 60 5 v325 := viaSmall (by decide +kernel) (by decide)

def v326 : List ℕ := [w0,w32,w1,w39,w3,w4]

theorem h331 : Ban 60 5 v326 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v327 : List ℕ := [w0,w32,w1,w3,w4,w45]

theorem h332 : Ban 60 5 v327 := viaSmall (by decide +kernel) (by decide)

def v328 : List ℕ := [w0,w32,w34,w2,w3,w4]

theorem h333 : Ban 60 5 v328 := viaSmall (by decide +kernel) (by decide)

def v329 : List ℕ := [w0,w32,w55,w2,w3,w4]

theorem h334 : Ban 60 5 v329 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v330 : List ℕ := [w0,w32,w2,w3,w42,w4]

theorem h335 : Ban 60 5 v330 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v331 : List ℕ := [w0,w32,w2,w3,w4,w48]

theorem h336 : Ban 60 5 v331 := viaSmall (by decide +kernel) (by decide)

def w89 : ℕ := 0x1b06c1b06c1b06cffffffffff00000

def v332 : List ℕ := [w0,w1,w89,w2,w3,w4]

theorem h337 : Ban 60 5 v332 := viaSmall (by decide +kernel) (by decide)

def v333 : List ℕ := [w0,w1,w2,w58,w3,w4]

theorem h338 : Ban 60 5 v333 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def w90 : ℕ := 0x9c2709c2709c270ffc00fffff003ff

def v334 : List ℕ := [w0,w1,w2,w3,w90,w4]

theorem h339 : Ban 60 5 v334 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def w91 : ℕ := 0xf03c0f03c0f03c0ffffffffff00000

def v335 : List ℕ := [w0,w1,w2,w3,w4,w91]

theorem h340 : Ban 60 5 v335 := viaSmall (by decide +kernel) (by decide)

def v336 : List ℕ := [w32,w1,w2,w65,w3,w4]

theorem h341 : Ban 60 5 v336 := viaSmall (by decide +kernel) (by decide)

def v337 : List ℕ := [w32,w1,w2,w3,w41,w4]

theorem h342 : Ban 60 5 v337 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h317 : Ban 60 6 v312 := viaBranch (ws := [v313,v314,v3,v4,v6,v8,v36,v82,v134,v168,v192,v225,v228,v257,v259,v289,v290,v315,v316,v317,v318,v319,v320,v321,v322,v323,v324,v325,v326,v327,v328,v329,v330,v331,v332,v333,v248,v334,v280,v335,v336,v337])
  (consBan h318 (consBan h319 (consBan h220 (consBan h221 (consBan h222 (consBan h225 (consBan h36 (consBan h82 (consBan h134 (consBan h227 (consBan h192 (consBan h230 (consBan h233 (consBan h262 (consBan h264 (consBan h294 (consBan h295 (consBan h320 (consBan h321 (consBan h322 (consBan h323 (consBan h324 (consBan h325 (consBan h326 (consBan h327 (consBan h328 (consBan h329 (consBan h330 (consBan h331 (consBan h332 (consBan h333 (consBan h334 (consBan h335 (consBan h336 (consBan h337 (consBan h338 (consBan h253 (consBan h339 (consBan h285 (consBan h340 (consBan h341 (consBan h342 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v338 : List ℕ := [w10,w0,w34,w2,w3,w4]

theorem h344 : Ban 60 5 v338 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v339 : List ℕ := [w10,w1,w34,w2,w3,w4]

theorem h345 : Ban 60 5 v339 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w92 : ℕ := 0xfffff0000000000

def v340 : List ℕ := [w92,w0,w1,w34,w2,w3]

theorem h346 : Ban 60 5 v340 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v341 : List ℕ := [w92,w0,w1,w2,w3]

theorem h347 : Ban 60 5 v341 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v342 : List ℕ := [w92,w0,w1,w2,w3,w4]

theorem h348 : Ban 60 5 v342 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w93 : ℕ := 0x200802008020080000000000ffc00

def v343 : List ℕ := [w93,w0,w1,w2,w3,w4]

theorem h349 : Ban 60 5 v343 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v344 : List ℕ := [w22,w1,w34,w2,w3,w4]

theorem h350 : Ban 60 5 v344 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w94 : ℕ := 0x8020080200802000000ffc0000000

def v345 : List ℕ := [w94,w0,w1,w2,w3,w4]

theorem h351 : Ban 60 5 v345 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v346 : List ℕ := [w24,w1,w34,w2,w3,w4]

theorem h352 : Ban 60 5 v346 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v347 : List ℕ := [w25,w1,w34,w2,w3,w4]

theorem h353 : Ban 60 5 v347 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v348 : List ℕ := [w26,w0,w34,w2,w3,w4]

theorem h354 : Ban 60 5 v348 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

theorem h355 : Ban 60 5 v284 := viaSmall (by decide +kernel) (by decide)

def w95 : ℕ := 0x1304c1304c1304cfffff003ffffc00

def v349 : List ℕ := [w0,w1,w95,w2,w3,w4]

theorem h356 : Ban 60 5 v349 := viaSmall (by decide +kernel) (by decide)

def w96 : ℕ := 0x190641906419064ffffffffff00000

def v350 : List ℕ := [w0,w1,w96,w2,w3,w4]

theorem h357 : Ban 60 5 v350 := viaSmall (by decide +kernel) (by decide)

def w97 : ℕ := 0x1b06c1b06c1b06c00000fffffffc00

def v351 : List ℕ := [w0,w1,w97,w34,w2,w3]

theorem h358 : Ban 60 5 v351 := viaSmall (by decide +kernel) (by decide)

def v352 : List ℕ := [w0,w1,w97,w2,w3]

def v353 : List ℕ := [w22,w1,w97,w2,w3]

theorem h360 : Ban 60 4 v353 := viaSmall (by decide +kernel) (by decide)

def v354 : List ℕ := [w24,w1,w97,w2,w3]

theorem h361 : Ban 60 4 v354 := viaSmall (by decide +kernel) (by decide)

def v355 : List ℕ := [w0,w30,w97,w2,w3]

theorem h362 : Ban 60 4 v355 := viaSmall (by decide +kernel) (by decide)

def v356 : List ℕ := [w0,w32,w97,w2,w3]

theorem h363 : Ban 60 4 v356 := viaSmall (by decide +kernel) (by decide)

def w98 : ℕ := 0x1304c1304c1304c00000003ffffc00

def v357 : List ℕ := [w0,w1,w98,w2,w3]

theorem h364 : Ban 60 4 v357 := viaSmall (by decide +kernel) (by decide)

def w99 : ℕ := 0x19064190641906400000fffff00000

def v358 : List ℕ := [w0,w1,w99,w2,w3]

theorem h365 : Ban 60 4 v358 := viaSmall (by decide +kernel) (by decide)

def v359 : List ℕ := [w0,w1,w97,w54,w3]

theorem h366 : Ban 60 4 v359 := viaSmall (by decide +kernel) (by decide)

def v360 : List ℕ := [w0,w1,w97,w2,w37]

theorem h367 : Ban 60 4 v360 := viaSmall (by decide +kernel) (by decide)

def v361 : List ℕ := [w0,w1,w97,w2,w41]

theorem h368 : Ban 60 4 v361 := viaSmall (by decide +kernel) (by decide)

def v362 : List ℕ := [w0,w1,w97,w65,w3]

theorem h369 : Ban 60 4 v362 := viaSmall (by decide +kernel) (by decide)

def w100 : ℕ := 0x5b96e5b96e5b96e00000ffffffffff

def v363 : List ℕ := [w0,w1,w2,w100,w3]

theorem h370 : Ban 60 4 v363 := viaSmall (by decide +kernel) (by decide)

def w101 : ℕ := 0x9f27c9f27c9f27c00000ffffffffff

def v364 : List ℕ := [w0,w1,w2,w3,w101]

theorem h371 : Ban 60 4 v364 := viaSmall (by decide +kernel) (by decide)

def v365 : List ℕ := [w0,w97,w2,w58,w3]

theorem h372 : Ban 60 4 v365 := viaSmall (by decide +kernel) (by decide)

def v366 : List ℕ := [w0,w97,w2,w3,w42]

theorem h373 : Ban 60 4 v366 := viaSmall (by decide +kernel) (by decide)

def v367 : List ℕ := [w1,w97,w2,w65,w3]

theorem h374 : Ban 60 4 v367 := viaSmall (by decide +kernel) (by decide)

def v368 : List ℕ := [w1,w97,w2,w3,w41]

theorem h375 : Ban 60 4 v368 := viaSmall (by decide +kernel) (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h359 : Ban 60 5 v352 := viaBranch (ws := [v353,v354,v355,v356,v357,v358,v359,v360,v361,v362,v363,v364,v365,v366,v367,v368])
  (consBan h360 (consBan h361 (consBan h362 (consBan h363 (consBan h364 (consBan h365 (consBan h366 (consBan h367 (consBan h368 (consBan h369 (consBan h370 (consBan h371 (consBan h372 (consBan h373 (consBan h374 (consBan h375 (nilBan _ _)))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v369 : List ℕ := [w0,w1,w97,w2,w3,w4]

theorem h376 : Ban 60 5 v369 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v370 : List ℕ := [w0,w1,w34,w54,w3,w4]

theorem h377 : Ban 60 5 v370 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v371 : List ℕ := [w0,w1,w34,w2,w35,w3]

theorem h378 : Ban 60 5 v371 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v372 : List ℕ := [w0,w1,w34,w2,w37,w4]

theorem h379 : Ban 60 5 v372 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v373 : List ℕ := [w0,w1,w34,w2,w3,w59]

theorem h380 : Ban 60 5 v373 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v374 : List ℕ := [w0,w1,w34,w2,w3,w45]

def w102 : ℕ := 0x20080200802008fffff00000ffc00

def v375 : List ℕ := [w102,w0,w1,w2,w3]

theorem h382 : Ban 60 4 v375 := viaSmall (by decide +kernel) (by decide)

def v376 : List ℕ := [w0,w34,w58,w3,w45]

theorem h383 : Ban 60 4 v376 := viaSmall (by decide +kernel) (by decide)

def v377 : List ℕ := [w1,w34,w2,w41,w45]

theorem h384 : Ban 60 4 v377 := viaSmall (by decide +kernel) (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h381 : Ban 60 5 v374 := viaBranch (ws := [v375,v358,v376,v377])
  (consBan h382 (consBan h365 (consBan h383 (consBan h384 (nilBan _ _)))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v378 : List ℕ := [w0,w1,w34,w2,w3,w47]

def w103 : ℕ := 0x80200802008020fffffffc0000000

def v379 : List ℕ := [w103,w0,w1,w2,w3]

theorem h386 : Ban 60 4 v379 := viaSmall (by decide +kernel) (by decide)

def v380 : List ℕ := [w0,w34,w2,w42,w47]

theorem h387 : Ban 60 4 v380 := viaSmall (by decide +kernel) (by decide)

def v381 : List ℕ := [w1,w34,w65,w3,w47]

theorem h388 : Ban 60 4 v381 := viaSmall (by decide +kernel) (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h385 : Ban 60 5 v378 := viaBranch (ws := [v379,v357,v380,v381])
  (consBan h386 (consBan h364 (consBan h387 (consBan h388 (nilBan _ _)))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v382 : List ℕ := [w0,w1,w34,w2,w41,w4]

theorem h389 : Ban 60 5 v382 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v383 : List ℕ := [w0,w1,w34,w2,w4,w47]

theorem h390 : Ban 60 5 v383 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v384 : List ℕ := [w0,w1,w34,w65,w3,w4]

theorem h391 : Ban 60 5 v384 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v385 : List ℕ := [w0,w1,w34,w3,w4,w45]

theorem h392 : Ban 60 5 v385 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w104 : ℕ := 0x4090240902409020000000000003ff

def v386 : List ℕ := [w0,w1,w104,w2,w3,w4]

theorem h393 : Ban 60 5 v386 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def w105 : ℕ := 0x5b96e5b96e5b96efffffffffffffff

def v387 : List ℕ := [w0,w1,w2,w105,w3,w4]

theorem h394 : Ban 60 5 v387 := viaSmall (by decide +kernel) (by decide)

def w106 : ℕ := 0x8421084210842100000000000003ff

def v388 : List ℕ := [w0,w1,w2,w106,w3,w4]

theorem h395 : Ban 60 5 v388 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def w107 : ℕ := 0x9f27c9f27c9f27cfffffffffffffff

def v389 : List ℕ := [w0,w1,w2,w3,w107,w4]

theorem h396 : Ban 60 5 v389 := viaSmall (by decide +kernel) (by decide)

def w108 : ℕ := 0xe0380e0380e0380000000000000000

def v390 : List ℕ := [w0,w1,w2,w3,w108,w4]

theorem h397 : Ban 60 5 v390 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w109 : ℕ := 0xfb3ecfb3ecfb3ecffffffffffffc00

def v391 : List ℕ := [w0,w1,w2,w3,w4,w109]

theorem h398 : Ban 60 5 v391 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v392 : List ℕ := [w0,w34,w2,w58,w3,w4]

def w110 : ℕ := 0x120481204812048ffc00fffffffc00

def v393 : List ℕ := [w0,w110,w2,w3,w4]

theorem h400 : Ban 60 4 v393 := viaSmall (by decide +kernel) (by decide)

def w111 : ℕ := 0x5294a5294a5294affc00003ffffc00

def v394 : List ℕ := [w0,w34,w2,w111,w4]

theorem h401 : Ban 60 4 v394 := viaSmall (by decide +kernel) (by decide)

def v395 : List ℕ := [w34,w2,w58,w41,w4]

theorem h402 : Ban 60 4 v395 := viaSmall (by decide +kernel) (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h399 : Ban 60 5 v392 := viaBranch (ws := [v393,v365,v394,v376,v395])
  (consBan h400 (consBan h372 (consBan h401 (consBan h383 (consBan h402 (nilBan _ _))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v396 : List ℕ := [w0,w34,w2,w3,w42,w4]

def w112 : ℕ := 0x180601806018060ffc00fffffffc00

def v397 : List ℕ := [w0,w112,w2,w3,w4]

theorem h404 : Ban 60 4 v397 := viaSmall (by decide +kernel) (by decide)

def w113 : ℕ := 0x9c2709c2709c270ffc00fffff00000

def v398 : List ℕ := [w0,w34,w3,w113,w4]

theorem h405 : Ban 60 4 v398 := viaSmall (by decide +kernel) (by decide)

def v399 : List ℕ := [w34,w65,w3,w42,w4]

theorem h406 : Ban 60 4 v399 := viaSmall (by decide +kernel) (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h403 : Ban 60 5 v396 := viaBranch (ws := [v397,v366,v380,v398,v399])
  (consBan h404 (consBan h373 (consBan h387 (consBan h405 (consBan h406 (nilBan _ _))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v400 : List ℕ := [w0,w34,w2,w3,w4,w48]

theorem h407 : Ban 60 5 v400 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v401 : List ℕ := [w1,w34,w2,w65,w3,w4]

theorem h408 : Ban 60 5 v401 := viaSmall (by decide +kernel) (by decide)

def v402 : List ℕ := [w1,w34,w2,w3,w41,w4]

theorem h409 : Ban 60 5 v402 := viaSmall (by decide +kernel) (by decide)

def v403 : List ℕ := [w1,w34,w2,w3,w4,w46]

theorem h410 : Ban 60 5 v403 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v404 : List ℕ := [w1,w34,w2,w41,w4]

def w114 : ℕ := 0xfffff00000

def v405 : List ℕ := [w114,w34,w2,w41,w4]

theorem h412 : Ban 60 4 v405 := viaSmall (by decide +kernel) (by decide)

def v406 : List ℕ := [w92,w1,w34,w2,w41]

theorem h413 : Ban 60 4 v406 := viaSmall (by decide +kernel) (by decide)

def v407 : List ℕ := [w18,w1,w34,w41,w4]

theorem h414 : Ban 60 4 v407 := viaSmall (by decide +kernel) (by decide)

def v408 : List ℕ := [w26,w1,w2,w41,w4]

theorem h415 : Ban 60 4 v408 := viaSmall (by decide +kernel) (by decide)

def v409 : List ℕ := [w26,w34,w2,w41,w4]

theorem h416 : Ban 60 4 v409 := viaSmall (by decide +kernel) (by decide)

def w115 : ℕ := 0xb02c0b02c0b02c003fffffff00000

def v410 : List ℕ := [w115,w1,w2,w41,w4]

theorem h417 : Ban 60 4 v410 := viaSmall (by decide +kernel) (by decide)

def w116 : ℕ := 0xf03c0f03c0f03c00000fffff003ff

def v411 : List ℕ := [w116,w1,w34,w2,w4]

theorem h418 : Ban 60 4 v411 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v412 : List ℕ := [w29,w34,w2,w41,w4]

theorem h419 : Ban 60 4 v412 := viaSmall (by decide +kernel) (by decide)

def v413 : List ℕ := [w32,w34,w2,w41,w4]

theorem h420 : Ban 60 4 v413 := viaSmall (by decide +kernel) (by decide)

def v414 : List ℕ := [w1,w97,w34,w2,w41]

theorem h421 : Ban 60 4 v414 := viaSmall (by decide +kernel) (by decide)

def v415 : List ℕ := [w1,w34,w2,w41,w59]

theorem h422 : Ban 60 4 v415 := viaSmall (by decide +kernel) (by decide)

def w117 : ℕ := 0xef3bcef3bcef3bcffffffffff003ff

def v416 : List ℕ := [w1,w34,w2,w4,w117]

theorem h423 : Ban 60 4 v416 := viaSmall (by decide +kernel) (by decide)

def v417 : List ℕ := [w1,w34,w41,w4,w45]

theorem h424 : Ban 60 4 v417 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v418 : List ℕ := [w1,w2,w106,w41,w4]

theorem h425 : Ban 60 4 v418 := viaSmall (by decide +kernel) (by decide)

def w118 : ℕ := 0x8f23c8f23c8f23c003ff00000003ff

def v419 : List ℕ := [w34,w2,w118,w41,w4]

theorem h426 : Ban 60 4 v419 := viaSmall (by decide +kernel) (by decide)

def v420 : List ℕ := [w34,w2,w41,w4,w48]

theorem h427 : Ban 60 4 v420 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h411 : Ban 60 5 v404 := viaBranch (ws := [v405,v406,v407,v408,v409,v410,v411,v412,v413,v414,v415,v377,v416,v417,v418,v395,v419,v420])
  (consBan h412 (consBan h413 (consBan h414 (consBan h415 (consBan h416 (consBan h417 (consBan h418 (consBan h419 (consBan h420 (consBan h421 (consBan h422 (consBan h384 (consBan h423 (consBan h424 (consBan h425 (consBan h402 (consBan h426 (consBan h427 (nilBan _ _)))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v421 : List ℕ := [w1,w34,w65,w3,w4]

def w119 : ℕ := 0x3ffffc00

def v422 : List ℕ := [w119,w34,w65,w3,w4]

theorem h429 : Ban 60 4 v422 := viaSmall (by decide +kernel) (by decide)

def v423 : List ℕ := [w92,w1,w34,w65,w3]

theorem h430 : Ban 60 4 v423 := viaSmall (by decide +kernel) (by decide)

def v424 : List ℕ := [w26,w1,w65,w3,w4]

theorem h431 : Ban 60 4 v424 := viaSmall (by decide +kernel) (by decide)

def v425 : List ℕ := [w26,w34,w65,w3,w4]

theorem h432 : Ban 60 4 v425 := viaSmall (by decide +kernel) (by decide)

def w120 : ℕ := 0xb02c0b02c0b02c003ff003ffffc00

def v426 : List ℕ := [w120,w1,w65,w3,w4]

theorem h433 : Ban 60 4 v426 := viaSmall (by decide +kernel) (by decide)

def w121 : ℕ := 0xb82e0b82e0b82e00000003fffffff

def v427 : List ℕ := [w121,w1,w34,w3,w4]

theorem h434 : Ban 60 4 v427 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v428 : List ℕ := [w28,w1,w34,w65,w4]

theorem h435 : Ban 60 4 v428 := viaSmall (by decide +kernel) (by decide)

def v429 : List ℕ := [w29,w34,w65,w3,w4]

theorem h436 : Ban 60 4 v429 := viaSmall (by decide +kernel) (by decide)

def v430 : List ℕ := [w30,w34,w65,w3,w4]

theorem h437 : Ban 60 4 v430 := viaSmall (by decide +kernel) (by decide)

def v431 : List ℕ := [w1,w97,w34,w65,w3]

theorem h438 : Ban 60 4 v431 := viaSmall (by decide +kernel) (by decide)

def v432 : List ℕ := [w1,w34,w65,w35,w3]

theorem h439 : Ban 60 4 v432 := viaSmall (by decide +kernel) (by decide)

def v433 : List ℕ := [w1,w34,w65,w4,w47]

theorem h440 : Ban 60 4 v433 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w122 : ℕ := 0xebbaeebbaeebbaefffff003fffffff

def v434 : List ℕ := [w1,w34,w3,w4,w122]

theorem h441 : Ban 60 4 v434 := viaSmall (by decide +kernel) (by decide)

def v435 : List ℕ := [w1,w104,w65,w3,w4]

theorem h442 : Ban 60 4 v435 := viaSmall (by decide +kernel) (by decide)

def w123 : ℕ := 0x4b92e4b92e4b92e003ff00000003ff

def v436 : List ℕ := [w34,w123,w65,w3,w4]

theorem h443 : Ban 60 4 v436 := viaSmall (by decide +kernel) (by decide)

def v437 : List ℕ := [w34,w65,w3,w4,w48]

theorem h444 : Ban 60 4 v437 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h428 : Ban 60 5 v421 := viaBranch (ws := [v422,v423,v424,v425,v426,v427,v428,v429,v430,v431,v432,v381,v433,v434,v435,v436,v399,v437])
  (consBan h429 (consBan h430 (consBan h431 (consBan h432 (consBan h433 (consBan h434 (consBan h435 (consBan h436 (consBan h437 (consBan h438 (consBan h439 (consBan h388 (consBan h440 (consBan h441 (consBan h442 (consBan h443 (consBan h406 (consBan h444 (nilBan _ _)))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h343 : Ban 60 6 v304 := viaBranch (ws := [v338,v339,v340,v341,v342,v343,v38,v344,v345,v346,v347,v168,v348,v193,v241,v273,v284,v328,v349,v350,v351,v352,v369,v370,v371,v372,v373,v374,v378,v382,v383,v384,v385,v386,v387,v388,v389,v390,v391,v392,v396,v400,v308,v401,v402,v403,v404,v421])
  (consBan h344 (consBan h345 (consBan h346 (consBan h347 (consBan h348 (consBan h349 (consBan h38 (consBan h350 (consBan h351 (consBan h352 (consBan h353 (consBan h227 (consBan h354 (consBan h193 (consBan h246 (consBan h278 (consBan h355 (consBan h333 (consBan h356 (consBan h357 (consBan h358 (consBan h359 (consBan h376 (consBan h377 (consBan h378 (consBan h379 (consBan h380 (consBan h381 (consBan h385 (consBan h389 (consBan h390 (consBan h391 (consBan h392 (consBan h393 (consBan h394 (consBan h395 (consBan h396 (consBan h397 (consBan h398 (consBan h399 (consBan h403 (consBan h407 (consBan h313 (consBan h408 (consBan h409 (consBan h410 (consBan h411 (consBan h428 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v438 : List ℕ := [w0,w1,w53,w2,w3,w4]

theorem h445 : Ban 60 6 v438 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v439 : List ℕ := [w0,w1,w54,w2,w3,w4]

theorem h446 : Ban 60 6 v439 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v440 : List ℕ := [w0,w1,w54,w3,w4]

def v441 : List ℕ := [w5,w0,w1,w54,w3,w4]

theorem h448 : Ban 60 5 v441 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v442 : List ℕ := [w9,w0,w1,w54,w3,w4]

theorem h449 : Ban 60 5 v442 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v443 : List ℕ := [w10,w0,w1,w54,w3,w4]

theorem h450 : Ban 60 5 v443 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v444 : List ℕ := [w14,w0,w1,w54,w3,w4]

theorem h451 : Ban 60 5 v444 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v445 : List ℕ := [w15,w0,w1,w54,w3,w4]

theorem h452 : Ban 60 5 v445 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v446 : List ℕ := [w16,w0,w1,w54,w3,w4]

theorem h453 : Ban 60 5 v446 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v447 : List ℕ := [w19,w0,w1,w54,w3,w4]

theorem h454 : Ban 60 5 v447 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v448 : List ℕ := [w22,w0,w1,w54,w3,w4]

theorem h455 : Ban 60 5 v448 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v449 : List ℕ := [w23,w0,w1,w54,w3,w4]

theorem h456 : Ban 60 5 v449 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v450 : List ℕ := [w25,w0,w1,w54,w3,w4]

theorem h457 : Ban 60 5 v450 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v451 : List ℕ := [w26,w0,w1,w54,w3,w4]

theorem h458 : Ban 60 5 v451 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v452 : List ℕ := [w0,w28,w1,w54,w3,w4]

theorem h459 : Ban 60 5 v452 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v453 : List ℕ := [w0,w1,w53,w54,w3,w4]

theorem h460 : Ban 60 5 v453 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v454 : List ℕ := [w0,w1,w104,w54,w3,w4]

theorem h461 : Ban 60 5 v454 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def w124 : ℕ := 0x4090240902409020000000000ffc00

def v455 : List ℕ := [w0,w1,w124,w54,w3,w4]

theorem h462 : Ban 60 5 v455 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v456 : List ℕ := [w0,w1,w54,w65,w3,w4]

theorem h463 : Ban 60 5 v456 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w125 : ℕ := 0x509425094250942ffc00ffffffffff

def v457 : List ℕ := [w0,w1,w54,w125,w3,w4]

theorem h464 : Ban 60 5 v457 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v458 : List ℕ := [w0,w1,w54,w35,w3]

theorem h465 : Ban 60 5 v458 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v459 : List ℕ := [w0,w1,w54,w35,w3,w4]

theorem h466 : Ban 60 5 v459 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v460 : List ℕ := [w0,w1,w54,w36,w3,w4]

theorem h467 : Ban 60 5 v460 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v461 : List ℕ := [w0,w1,w54,w37,w3,w4]

theorem h468 : Ban 60 5 v461 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v462 : List ℕ := [w0,w1,w54,w37,w4]

theorem h469 : Ban 60 5 v462 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v463 : List ℕ := [w0,w1,w54,w38,w3,w4]

theorem h470 : Ban 60 5 v463 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v464 : List ℕ := [w0,w1,w54,w39,w3,w4]

theorem h471 : Ban 60 5 v464 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v465 : List ℕ := [w0,w1,w54,w3,w41,w4]

theorem h472 : Ban 60 5 v465 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v466 : List ℕ := [w0,w1,w54,w3,w42,w4]

theorem h473 : Ban 60 5 v466 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v467 : List ℕ := [w0,w1,w54,w3,w59]

theorem h474 : Ban 60 5 v467 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v468 : List ℕ := [w0,w1,w54,w3,w59,w4]

theorem h475 : Ban 60 5 v468 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w126 : ℕ := 0xccb32ccb32ccb3200000ffc00fffff

def v469 : List ℕ := [w0,w1,w54,w3,w126,w4]

theorem h476 : Ban 60 5 v469 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v470 : List ℕ := [w0,w1,w54,w3,w43,w4]

theorem h477 : Ban 60 5 v470 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v471 : List ℕ := [w0,w1,w54,w3,w44,w4]

theorem h478 : Ban 60 5 v471 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w127 : ℕ := 0xe0b82e0b82e0b82fffff00000fffff

def v472 : List ℕ := [w0,w1,w54,w3,w4,w127]

theorem h479 : Ban 60 5 v472 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v473 : List ℕ := [w0,w1,w54,w3,w4,w46]

theorem h480 : Ban 60 5 v473 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v474 : List ℕ := [w0,w1,w54,w3,w4,w47]

theorem h481 : Ban 60 5 v474 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v475 : List ℕ := [w0,w1,w54,w3,w4,w48]

theorem h482 : Ban 60 5 v475 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v476 : List ℕ := [w0,w1,w54,w3,w127]

theorem h483 : Ban 60 5 v476 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v477 : List ℕ := [w0,w1,w54,w3,w47]

theorem h484 : Ban 60 5 v477 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v478 : List ℕ := [w0,w1,w54,w41,w4]

theorem h485 : Ban 60 5 v478 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v479 : List ℕ := [w0,w1,w54,w4,w47]

theorem h486 : Ban 60 5 v479 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v480 : List ℕ := [w0,w1,w65,w3,w4]

theorem h487 : Ban 60 5 v480 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v481 : List ℕ := [w0,w1,w3,w4,w127]

theorem h488 : Ban 60 5 v481 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v482 : List ℕ := [w1,w54,w65,w3,w4]

theorem h489 : Ban 60 5 v482 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v483 : List ℕ := [w1,w54,w3,w41,w4]

theorem h490 : Ban 60 5 v483 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h447 : Ban 60 6 v440 := viaBranch (ws := [v441,v442,v443,v444,v445,v446,v447,v19,v448,v86,v449,v450,v451,v452,v197,v229,v260,v291,v315,v370,v453,v454,v455,v456,v457,v458,v459,v460,v461,v462,v463,v464,v465,v466,v467,v468,v469,v470,v471,v472,v473,v474,v475,v476,v477,v478,v479,v480,v481,v482,v483])
  (consBan h448 (consBan h449 (consBan h450 (consBan h451 (consBan h452 (consBan h453 (consBan h454 (consBan h19 (consBan h455 (consBan h86 (consBan h456 (consBan h457 (consBan h458 (consBan h459 (consBan h197 (consBan h234 (consBan h265 (consBan h296 (consBan h320 (consBan h377 (consBan h460 (consBan h461 (consBan h462 (consBan h463 (consBan h464 (consBan h465 (consBan h466 (consBan h467 (consBan h468 (consBan h469 (consBan h470 (consBan h471 (consBan h472 (consBan h473 (consBan h474 (consBan h475 (consBan h476 (consBan h477 (consBan h478 (consBan h479 (consBan h480 (consBan h481 (consBan h482 (consBan h483 (consBan h484 (consBan h485 (consBan h486 (consBan h487 (consBan h488 (consBan h489 (consBan h490 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

theorem h491 : Ban 60 6 v246 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v484 : List ℕ := [w0,w1,w56,w2,w3,w4]

theorem h492 : Ban 60 6 v484 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v485 : List ℕ := [w0,w1,w2,w65,w3,w4]

def v486 : List ℕ := [w5,w0,w1,w65,w3,w4]

theorem h494 : Ban 60 5 v486 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v487 : List ℕ := [w9,w0,w1,w65,w3,w4]

theorem h495 : Ban 60 5 v487 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v488 : List ℕ := [w10,w1,w2,w65,w3,w4]

theorem h496 : Ban 60 5 v488 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v489 : List ℕ := [w119,w0,w1,w2,w3,w4]

theorem h497 : Ban 60 5 v489 := viaSmall (by decide +kernel) (by decide)

def v490 : List ℕ := [w15,w1,w2,w65,w3,w4]

theorem h498 : Ban 60 5 v490 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v491 : List ℕ := [w17,w0,w1,w65,w3,w4]

theorem h499 : Ban 60 5 v491 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v492 : List ℕ := [w17,w1,w2,w65,w3,w4]

theorem h500 : Ban 60 5 v492 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v493 : List ℕ := [w18,w0,w1,w65,w3,w4]

theorem h501 : Ban 60 5 v493 := viaSmall (by decide +kernel) (by decide)

def v494 : List ℕ := [w22,w1,w2,w65,w3,w4]

theorem h502 : Ban 60 5 v494 := viaSmall (by decide +kernel) (by decide)

def v495 : List ℕ := [w23,w1,w2,w65,w3,w4]

theorem h503 : Ban 60 5 v495 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w128 : ℕ := 0x802008020080200000000000003ff

def v496 : List ℕ := [w128,w0,w1,w2,w3,w4]

theorem h504 : Ban 60 5 v496 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

theorem h505 : Ban 60 5 v116 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v497 : List ℕ := [w24,w0,w1,w65,w3,w4]

theorem h506 : Ban 60 5 v497 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v498 : List ℕ := [w25,w1,w2,w65,w3,w4]

theorem h507 : Ban 60 5 v498 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v499 : List ℕ := [w26,w1,w2,w65,w3,w4]

theorem h508 : Ban 60 5 v499 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v500 : List ℕ := [w0,w121,w1,w2,w3,w4]

theorem h509 : Ban 60 5 v500 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v501 : List ℕ := [w0,w1,w53,w65,w3,w4]

theorem h510 : Ban 60 5 v501 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w129 : ℕ := 0x401004010040100003ff0000000000

def v502 : List ℕ := [w0,w1,w129,w2,w3,w4]

theorem h511 : Ban 60 5 v502 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

theorem h512 : Ban 60 5 v439 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v503 : List ℕ := [w0,w1,w55,w65,w3,w4]

theorem h513 : Ban 60 5 v503 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v504 : List ℕ := [w0,w1,w56,w65,w3,w4]

theorem h514 : Ban 60 5 v504 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def w130 : ℕ := 0x4390e4390e4390e003ff003ffffc00

def v505 : List ℕ := [w0,w1,w2,w130,w3,w4]

theorem h515 : Ban 60 5 v505 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v506 : List ℕ := [w0,w1,w2,w123,w3,w4]

theorem h516 : Ban 60 5 v506 := viaSmall (by decide +kernel) (by decide)

def v507 : List ℕ := [w0,w1,w2,w65,w35,w3]

theorem h517 : Ban 60 5 v507 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v508 : List ℕ := [w0,w1,w2,w65,w37,w4]

theorem h518 : Ban 60 5 v508 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v509 : List ℕ := [w0,w1,w2,w65,w3,w59]

theorem h519 : Ban 60 5 v509 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v510 : List ℕ := [w0,w1,w2,w65,w3,w45]

theorem h520 : Ban 60 5 v510 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v511 : List ℕ := [w0,w1,w2,w65,w3,w47]

theorem h521 : Ban 60 5 v511 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v512 : List ℕ := [w0,w1,w2,w65,w41,w4]

theorem h522 : Ban 60 5 v512 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v513 : List ℕ := [w0,w1,w2,w65,w4,w47]

theorem h523 : Ban 60 5 v513 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w131 : ℕ := 0x84210842108421000000ffc0000000

def v514 : List ℕ := [w0,w1,w2,w131,w3,w4]

theorem h524 : Ban 60 5 v514 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def w132 : ℕ := 0xa0280a0280a0280ffc000000000000

def v515 : List ℕ := [w0,w1,w2,w3,w132,w4]

theorem h525 : Ban 60 5 v515 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w133 : ℕ := 0xcfb3ecfb3ecfb3e003ffffffffffff

def v516 : List ℕ := [w0,w1,w2,w3,w133,w4]

theorem h526 : Ban 60 5 v516 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v517 : List ℕ := [w0,w1,w2,w3,w4,w122]

theorem h527 : Ban 60 5 v517 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v518 : List ℕ := [w0,w1,w65,w58,w3,w4]

theorem h528 : Ban 60 5 v518 := viaSmall (by decide +kernel) (by decide)

def v519 : List ℕ := [w0,w1,w65,w39,w3,w4]

theorem h529 : Ban 60 5 v519 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v520 : List ℕ := [w0,w1,w65,w3,w59]

theorem h530 : Ban 60 5 v520 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v521 : List ℕ := [w0,w1,w65,w3,w59,w4]

theorem h531 : Ban 60 5 v521 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v522 : List ℕ := [w0,w1,w65,w3,w60,w4]

theorem h532 : Ban 60 5 v522 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v523 : List ℕ := [w0,w1,w65,w3,w4,w45]

theorem h533 : Ban 60 5 v523 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v524 : List ℕ := [w1,w54,w2,w65,w3,w4]

theorem h534 : Ban 60 5 v524 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v525 : List ℕ := [w1,w2,w65,w37,w3,w4]

theorem h535 : Ban 60 5 v525 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v526 : List ℕ := [w1,w2,w65,w37,w4]

theorem h536 : Ban 60 5 v526 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v527 : List ℕ := [w1,w2,w65,w3,w41,w4]

theorem h537 : Ban 60 5 v527 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v528 : List ℕ := [w1,w2,w65,w3,w44,w4]

theorem h538 : Ban 60 5 v528 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v529 : List ℕ := [w1,w2,w65,w3,w4,w46]

theorem h539 : Ban 60 5 v529 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h493 : Ban 60 6 v485 := viaBranch (ws := [v486,v487,v488,v489,v490,v491,v492,v493,v494,v495,v496,v116,v497,v139,v163,v498,v499,v500,v200,v289,v324,v501,v502,v439,v456,v503,v504,v505,v506,v507,v508,v509,v510,v511,v512,v513,v387,v514,v515,v516,v517,v518,v519,v520,v521,v522,v523,v309,v401,v524,v482,v525,v526,v527,v528,v529])
  (consBan h494 (consBan h495 (consBan h496 (consBan h497 (consBan h498 (consBan h499 (consBan h500 (consBan h501 (consBan h502 (consBan h503 (consBan h504 (consBan h505 (consBan h506 (consBan h139 (consBan h163 (consBan h507 (consBan h508 (consBan h509 (consBan h200 (consBan h294 (consBan h329 (consBan h510 (consBan h511 (consBan h512 (consBan h463 (consBan h513 (consBan h514 (consBan h515 (consBan h516 (consBan h517 (consBan h518 (consBan h519 (consBan h520 (consBan h521 (consBan h522 (consBan h523 (consBan h394 (consBan h524 (consBan h525 (consBan h526 (consBan h527 (consBan h528 (consBan h529 (consBan h530 (consBan h531 (consBan h532 (consBan h533 (consBan h314 (consBan h408 (consBan h534 (consBan h489 (consBan h535 (consBan h536 (consBan h537 (consBan h538 (consBan h539 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v530 : List ℕ := [w9,w0,w1,w58,w3,w4]

theorem h541 : Ban 60 5 v530 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v531 : List ℕ := [w9,w0,w2,w58,w3,w4]

theorem h542 : Ban 60 5 v531 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def w134 : ℕ := 0xffc00003ff

def v532 : List ℕ := [w134,w0,w1,w2,w58,w4]

theorem h543 : Ban 60 5 v532 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v533 : List ℕ := [w134,w0,w1,w2,w3,w4]

theorem h544 : Ban 60 5 v533 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v534 : List ℕ := [w134,w0,w1,w2,w4]

theorem h545 : Ban 60 5 v534 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def w135 : ℕ := 0x2008020080200800000003ff00000

def v535 : List ℕ := [w135,w0,w1,w2,w3,w4]

theorem h546 : Ban 60 5 v535 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v536 : List ℕ := [w18,w0,w1,w58,w3,w4]

theorem h547 : Ban 60 5 v536 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v537 : List ℕ := [w63,w0,w1,w2,w3,w4]

theorem h548 : Ban 60 5 v537 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

theorem h549 : Ban 60 5 v312 := viaSmall (by decide +kernel) (by decide)

def w136 : ℕ := 0x1284a1284a1284a00000ffffffffff

def v538 : List ℕ := [w0,w1,w136,w2,w3,w4]

theorem h550 : Ban 60 5 v538 := viaSmall (by decide +kernel) (by decide)

def w137 : ℕ := 0x401004010040100ffc000000000000

def v539 : List ℕ := [w0,w1,w137,w2,w3,w4]

theorem h551 : Ban 60 5 v539 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v540 : List ℕ := [w0,w1,w54,w58,w3,w4]

theorem h552 : Ban 60 5 v540 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v541 : List ℕ := [w0,w1,w56,w58,w3,w4]

theorem h553 : Ban 60 5 v541 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def w138 : ℕ := 0x509425094250942ffc00ffc00fffff

def v542 : List ℕ := [w0,w1,w2,w138,w3,w4]

theorem h554 : Ban 60 5 v542 := viaSmall (by decide +kernel) (by decide)

def v543 : List ℕ := [w0,w1,w2,w111,w58,w4]

theorem h555 : Ban 60 5 v543 := viaSmall (by decide +kernel) (by decide)

def v544 : List ℕ := [w0,w1,w2,w111,w3,w4]

theorem h556 : Ban 60 5 v544 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v545 : List ℕ := [w0,w1,w2,w111,w4]

def v546 : List ℕ := [w18,w0,w1,w111,w4]

theorem h558 : Ban 60 4 v546 := viaSmall (by decide +kernel) (by decide)

def v547 : List ℕ := [w24,w1,w2,w111,w4]

theorem h559 : Ban 60 4 v547 := viaSmall (by decide +kernel) (by decide)

def v548 : List ℕ := [w0,w29,w2,w111,w4]

theorem h560 : Ban 60 4 v548 := viaSmall (by decide +kernel) (by decide)

def v549 : List ℕ := [w0,w31,w2,w111,w4]

theorem h561 : Ban 60 4 v549 := viaSmall (by decide +kernel) (by decide)

def w139 : ℕ := 0x1284a1284a1284a00000003ffffc00

def v550 : List ℕ := [w0,w1,w139,w2,w4]

theorem h562 : Ban 60 4 v550 := viaSmall (by decide +kernel) (by decide)

def v551 : List ℕ := [w0,w1,w54,w111,w4]

theorem h563 : Ban 60 4 v551 := viaSmall (by decide +kernel) (by decide)

def w140 : ℕ := 0x509425094250942ffc0000000ffc00

def v552 : List ℕ := [w0,w1,w2,w140,w4]

theorem h564 : Ban 60 4 v552 := viaSmall (by decide +kernel) (by decide)

def v553 : List ℕ := [w0,w1,w2,w111,w59]

theorem h565 : Ban 60 4 v553 := viaSmall (by decide +kernel) (by decide)

def v554 : List ℕ := [w0,w1,w2,w111,w45]

theorem h566 : Ban 60 4 v554 := viaSmall (by decide +kernel) (by decide)

def w141 : ℕ := 0x5b96e5b96e5b96efffff003ffffc00

def v555 : List ℕ := [w0,w1,w2,w141,w4]

theorem h567 : Ban 60 4 v555 := viaSmall (by decide +kernel) (by decide)

def w142 : ℕ := 0xf2bcaf2bcaf2bcafffff003ffffc00

def v556 : List ℕ := [w0,w1,w2,w4,w142]

theorem h568 : Ban 60 4 v556 := viaSmall (by decide +kernel) (by decide)

def v557 : List ℕ := [w0,w1,w65,w111,w4]

theorem h569 : Ban 60 4 v557 := viaSmall (by decide +kernel) (by decide)

def v558 : List ℕ := [w0,w1,w111,w4,w45]

theorem h570 : Ban 60 4 v558 := viaSmall (by decide +kernel) (by decide)

def v559 : List ℕ := [w0,w2,w111,w4,w48]

theorem h571 : Ban 60 4 v559 := viaSmall (by decide +kernel) (by decide)

def v560 : List ℕ := [w1,w2,w65,w111,w4]

theorem h572 : Ban 60 4 v560 := viaSmall (by decide +kernel) (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h557 : Ban 60 5 v545 := viaBranch (ws := [v546,v547,v548,v549,v550,v551,v552,v553,v554,v555,v556,v557,v558,v394,v559,v560])
  (consBan h558 (consBan h559 (consBan h560 (consBan h561 (consBan h562 (consBan h563 (consBan h564 (consBan h565 (consBan h566 (consBan h567 (consBan h568 (consBan h569 (consBan h570 (consBan h401 (consBan h571 (consBan h572 (nilBan _ _)))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v561 : List ℕ := [w0,w1,w2,w58,w35,w3]

theorem h573 : Ban 60 5 v561 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v562 : List ℕ := [w0,w1,w2,w58,w37,w4]

theorem h574 : Ban 60 5 v562 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v563 : List ℕ := [w0,w1,w2,w58,w3,w59]

theorem h575 : Ban 60 5 v563 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v564 : List ℕ := [w0,w1,w2,w58,w3,w45]

theorem h576 : Ban 60 5 v564 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v565 : List ℕ := [w0,w1,w2,w58,w3,w47]

theorem h577 : Ban 60 5 v565 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v566 : List ℕ := [w0,w1,w2,w58,w41,w4]

def w143 : ℕ := 0x2008020080200800000fffff003ff

def v567 : List ℕ := [w143,w0,w1,w2,w4]

theorem h579 : Ban 60 4 v567 := viaSmall (by decide +kernel) (by decide)

def v568 : List ℕ := [w0,w1,w58,w41,w45]

theorem h580 : Ban 60 4 v568 := viaSmall (by decide +kernel) (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h578 : Ban 60 5 v566 := viaBranch (ws := [v567,v552,v568,v395])
  (consBan h579 (consBan h564 (consBan h580 (consBan h402 (nilBan _ _)))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v569 : List ℕ := [w0,w1,w2,w58,w4,w47]

def w144 : ℕ := 0x401004010040100ffc00ffc00003ff

def v570 : List ℕ := [w0,w1,w144,w2,w4]

theorem h582 : Ban 60 4 v570 := viaSmall (by decide +kernel) (by decide)

def v571 : List ℕ := [w0,w2,w58,w47,w48]

theorem h583 : Ban 60 4 v571 := viaSmall (by decide +kernel) (by decide)

def v572 : List ℕ := [w1,w65,w58,w4,w47]

theorem h584 : Ban 60 4 v572 := viaSmall (by decide +kernel) (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h581 : Ban 60 5 v569 := viaBranch (ws := [v550,v570,v571,v572])
  (consBan h562 (consBan h582 (consBan h583 (consBan h584 (nilBan _ _)))))
  (by decide) (by decide +kernel) (by decide +kernel)

def w145 : ℕ := 0x8c2308c2308c230000000000000000

def v573 : List ℕ := [w0,w1,w2,w145,w3,w4]

theorem h585 : Ban 60 5 v573 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def w146 : ℕ := 0xa0280a0280a0280003ff0000000000

def v574 : List ℕ := [w0,w1,w2,w3,w146,w4]

theorem h586 : Ban 60 5 v574 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w147 : ℕ := 0xdeb7adeb7adeb7affc00ffffffffff

def v575 : List ℕ := [w0,w1,w2,w3,w147,w4]

theorem h587 : Ban 60 5 v575 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def w148 : ℕ := 0xf2bcaf2bcaf2bcafffffffffffffff

def v576 : List ℕ := [w0,w1,w2,w3,w4,w148]

theorem h588 : Ban 60 5 v576 := viaSmall (by decide +kernel) (by decide)

def v577 : List ℕ := [w0,w1,w58,w3,w60,w4]

theorem h589 : Ban 60 5 v577 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v578 : List ℕ := [w0,w1,w58,w3,w4,w45]

theorem h590 : Ban 60 5 v578 := viaSmall (by decide +kernel) (by decide)

def v579 : List ℕ := [w0,w1,w58,w3,w45]

def v580 : List ℕ := [w134,w0,w1,w58,w45]

theorem h592 : Ban 60 4 v580 := viaSmall (by decide +kernel) (by decide)

def w149 : ℕ := 0xffc0000000ffc00

def v581 : List ℕ := [w149,w0,w58,w3,w45]

theorem h593 : Ban 60 4 v581 := viaSmall (by decide +kernel) (by decide)

def v582 : List ℕ := [w22,w1,w58,w3,w45]

theorem h594 : Ban 60 4 v582 := viaSmall (by decide +kernel) (by decide)

def v583 : List ℕ := [w0,w30,w58,w3,w45]

theorem h595 : Ban 60 4 v583 := viaSmall (by decide +kernel) (by decide)

def v584 : List ℕ := [w0,w31,w58,w3,w45]

theorem h596 : Ban 60 4 v584 := viaSmall (by decide +kernel) (by decide)

def v585 : List ℕ := [w0,w1,w55,w3,w45]

theorem h597 : Ban 60 4 v585 := viaSmall (by decide +kernel) (by decide)

def w150 : ℕ := 0x4290a4290a4290affc0000000fffff

def v586 : List ℕ := [w0,w1,w150,w3,w45]

theorem h598 : Ban 60 4 v586 := viaSmall (by decide +kernel) (by decide)

def v587 : List ℕ := [w0,w1,w111,w58,w45]

theorem h599 : Ban 60 4 v587 := viaSmall (by decide +kernel) (by decide)

def w151 : ℕ := 0x6298a6298a6298afffff00000ffc00

def v588 : List ℕ := [w0,w1,w58,w151,w3]

theorem h600 : Ban 60 4 v588 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v589 : List ℕ := [w0,w1,w58,w37,w45]

theorem h601 : Ban 60 4 v589 := viaSmall (by decide +kernel) (by decide)

def w152 : ℕ := 0xeebbaeebbaeebbafffffffc00fffff

def v590 : List ℕ := [w0,w1,w58,w3,w152]

theorem h602 : Ban 60 4 v590 := viaSmall (by decide +kernel) (by decide)

def v591 : List ℕ := [w0,w1,w3,w146,w45]

theorem h603 : Ban 60 4 v591 := viaSmall (by decide +kernel) (by decide)

def v592 : List ℕ := [w0,w55,w58,w3,w45]

theorem h604 : Ban 60 4 v592 := viaSmall (by decide +kernel) (by decide)

def v593 : List ℕ := [w0,w58,w3,w42,w45]

theorem h605 : Ban 60 4 v593 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def w153 : ℕ := 0xe2b8ae2b8ae2b8a003ff00000003ff

def v594 : List ℕ := [w0,w58,w3,w153,w45]

theorem h606 : Ban 60 4 v594 := viaSmall (by decide +kernel) (by decide)

def v595 : List ℕ := [w1,w58,w3,w41,w45]

theorem h607 : Ban 60 4 v595 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h591 : Ban 60 5 v579 := viaBranch (ws := [v580,v581,v582,v583,v584,v585,v586,v587,v588,v589,v590,v568,v591,v376,v592,v593,v594,v595])
  (consBan h592 (consBan h593 (consBan h594 (consBan h595 (consBan h596 (consBan h597 (consBan h598 (consBan h599 (consBan h600 (consBan h601 (consBan h602 (consBan h580 (consBan h603 (consBan h383 (consBan h604 (consBan h605 (consBan h606 (consBan h607 (nilBan _ _)))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v596 : List ℕ := [w0,w55,w2,w58,w3,w4]

theorem h608 : Ban 60 5 v596 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v597 : List ℕ := [w0,w2,w58,w3,w42,w4]

theorem h609 : Ban 60 5 v597 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v598 : List ℕ := [w0,w2,w58,w3,w4,w48]

def w154 : ℕ := 0x501405014050140ffc00fffffffc00

def v599 : List ℕ := [w0,w2,w154,w3,w4]

theorem h611 : Ban 60 4 v599 := viaSmall (by decide +kernel) (by decide)

def w155 : ℕ := 0xf03c0f03c0f03c0ffc00ffc00ffc00

def v600 : List ℕ := [w2,w58,w3,w4,w155]

theorem h612 : Ban 60 4 v600 := viaSmall (by decide +kernel) (by decide)

def v601 : List ℕ := [w65,w58,w3,w4,w48]

theorem h613 : Ban 60 4 v601 := viaSmall (by decide +kernel) (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h610 : Ban 60 5 v598 := viaBranch (ws := [v599,v559,v571,v600,v601])
  (consBan h611 (consBan h571 (consBan h583 (consBan h612 (consBan h613 (nilBan _ _))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v602 : List ℕ := [w1,w2,w65,w58,w3,w4]

theorem h614 : Ban 60 5 v602 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v603 : List ℕ := [w1,w2,w58,w3,w41,w4]

theorem h615 : Ban 60 5 v603 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v604 : List ℕ := [w1,w65,w58,w3,w4]

def v605 : List ℕ := [w119,w65,w58,w3,w4]

theorem h617 : Ban 60 4 v605 := viaSmall (by decide +kernel) (by decide)

def v606 : List ℕ := [w134,w1,w65,w58,w4]

theorem h618 : Ban 60 4 v606 := viaSmall (by decide +kernel) (by decide)

def v607 : List ℕ := [w63,w1,w65,w3,w4]

theorem h619 : Ban 60 4 v607 := viaSmall (by decide +kernel) (by decide)

def v608 : List ℕ := [w28,w1,w65,w58,w4]

theorem h620 : Ban 60 4 v608 := viaSmall (by decide +kernel) (by decide)

def v609 : List ℕ := [w29,w65,w58,w3,w4]

theorem h621 : Ban 60 4 v609 := viaSmall (by decide +kernel) (by decide)

def v610 : List ℕ := [w30,w65,w58,w3,w4]

theorem h622 : Ban 60 4 v610 := viaSmall (by decide +kernel) (by decide)

def v611 : List ℕ := [w1,w55,w65,w3,w4]

theorem h623 : Ban 60 4 v611 := viaSmall (by decide +kernel) (by decide)

def w156 : ℕ := 0x4290a4290a4290a00000003fffffff

def v612 : List ℕ := [w1,w156,w65,w3,w4]

theorem h624 : Ban 60 4 v612 := viaSmall (by decide +kernel) (by decide)

def v613 : List ℕ := [w1,w130,w58,w3,w4]

theorem h625 : Ban 60 4 v613 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v614 : List ℕ := [w1,w65,w111,w58,w4]

theorem h626 : Ban 60 4 v614 := viaSmall (by decide +kernel) (by decide)

def v615 : List ℕ := [w1,w65,w58,w35,w3]

theorem h627 : Ban 60 4 v615 := viaSmall (by decide +kernel) (by decide)

def v616 : List ℕ := [w1,w65,w58,w3,w47]

theorem h628 : Ban 60 4 v616 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v617 : List ℕ := [w1,w58,w3,w133,w4]

theorem h629 : Ban 60 4 v617 := viaSmall (by decide +kernel) (by decide)

def v618 : List ℕ := [w55,w65,w58,w3,w4]

theorem h630 : Ban 60 4 v618 := viaSmall (by decide +kernel) (by decide)

def v619 : List ℕ := [w123,w65,w58,w3,w4]

theorem h631 : Ban 60 4 v619 := viaSmall (by decide +kernel) (by decide)

def v620 : List ℕ := [w65,w58,w3,w42,w4]

theorem h632 : Ban 60 4 v620 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h616 : Ban 60 5 v604 := viaBranch (ws := [v605,v606,v607,v608,v609,v610,v611,v612,v613,v614,v615,v616,v572,v617,v618,v619,v620,v601])
  (consBan h617 (consBan h618 (consBan h619 (consBan h620 (consBan h621 (consBan h622 (consBan h623 (consBan h624 (consBan h625 (consBan h626 (consBan h627 (consBan h628 (consBan h584 (consBan h629 (consBan h630 (consBan h631 (consBan h632 (consBan h613 (nilBan _ _)))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h540 : Ban 60 6 v333 := viaBranch (ws := [v530,v531,v532,v533,v534,v535,v536,v90,v537,v140,v202,v242,v274,v301,v312,v325,v538,v539,v540,v246,v541,v542,v543,v544,v545,v561,v562,v563,v564,v565,v566,v569,v387,v573,v574,v575,v576,v518,v577,v578,v579,v392,v596,v597,v598,v602,v603,v604])
  (consBan h541 (consBan h542 (consBan h543 (consBan h544 (consBan h545 (consBan h546 (consBan h547 (consBan h90 (consBan h548 (consBan h140 (consBan h202 (consBan h247 (consBan h279 (consBan h306 (consBan h549 (consBan h330 (consBan h550 (consBan h551 (consBan h552 (consBan h251 (consBan h553 (consBan h554 (consBan h555 (consBan h556 (consBan h557 (consBan h573 (consBan h574 (consBan h575 (consBan h576 (consBan h577 (consBan h578 (consBan h581 (consBan h394 (consBan h585 (consBan h586 (consBan h587 (consBan h588 (consBan h528 (consBan h589 (consBan h590 (consBan h591 (consBan h399 (consBan h608 (consBan h609 (consBan h610 (consBan h614 (consBan h615 (consBan h616 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v621 : List ℕ := [w0,w1,w2,w35,w3]

def v622 : List ℕ := [w5,w0,w1,w2,w35,w3]

theorem h634 : Ban 60 5 v622 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v623 : List ℕ := [w9,w0,w1,w2,w35,w3]

theorem h635 : Ban 60 5 v623 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v624 : List ℕ := [w10,w0,w1,w2,w35,w3]

theorem h636 : Ban 60 5 v624 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v625 : List ℕ := [w14,w0,w1,w2,w35,w3]

theorem h637 : Ban 60 5 v625 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v626 : List ℕ := [w15,w0,w1,w2,w35,w3]

theorem h638 : Ban 60 5 v626 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v627 : List ℕ := [w16,w0,w1,w2,w35,w3]

theorem h639 : Ban 60 5 v627 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v628 : List ℕ := [w17,w0,w1,w2,w35,w3]

theorem h640 : Ban 60 5 v628 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v629 : List ℕ := [w18,w0,w1,w2,w35,w3]

theorem h641 : Ban 60 5 v629 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v630 : List ℕ := [w22,w0,w1,w2,w35,w3]

theorem h642 : Ban 60 5 v630 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v631 : List ℕ := [w23,w0,w1,w2,w35,w3]

theorem h643 : Ban 60 5 v631 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v632 : List ℕ := [w24,w0,w1,w2,w35,w3]

theorem h644 : Ban 60 5 v632 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v633 : List ℕ := [w25,w0,w1,w2,w35,w3]

theorem h645 : Ban 60 5 v633 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v634 : List ℕ := [w26,w0,w1,w2,w35,w3]

theorem h646 : Ban 60 5 v634 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w157 : ℕ := 0x200802008020080fffff0000000000

def v635 : List ℕ := [w0,w1,w157,w2,w35,w3]

theorem h647 : Ban 60 5 v635 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v636 : List ℕ := [w0,w1,w157,w2,w3]

theorem h648 : Ban 60 5 v636 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v637 : List ℕ := [w0,w1,w53,w2,w35,w3]

theorem h649 : Ban 60 5 v637 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v638 : List ℕ := [w0,w1,w54,w2,w35,w3]

theorem h650 : Ban 60 5 v638 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v639 : List ℕ := [w0,w1,w55,w2,w35,w3]

theorem h651 : Ban 60 5 v639 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v640 : List ℕ := [w0,w1,w56,w2,w35,w3]

theorem h652 : Ban 60 5 v640 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def w158 : ℕ := 0x601806018060180003ff0000000000

def v641 : List ℕ := [w0,w1,w2,w158,w35,w3]

theorem h653 : Ban 60 5 v641 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w159 : ℕ := 0x601806018060180ffc000000000000

def v642 : List ℕ := [w0,w1,w2,w159,w35,w3]

theorem h654 : Ban 60 5 v642 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w160 : ℕ := 0x6298a6298a6298afffff00000fffff

def v643 : List ℕ := [w0,w1,w2,w35,w160,w3]

theorem h655 : Ban 60 5 v643 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w161 : ℕ := 0x6b1ac6b1ac6b1acfffff003ff00000

def v644 : List ℕ := [w0,w1,w2,w35,w161,w3]

theorem h656 : Ban 60 5 v644 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w162 : ℕ := 0x701c0701c0701c0ffffffffffffc00

def v645 : List ℕ := [w0,w1,w2,w35,w162,w3]

theorem h657 : Ban 60 5 v645 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v646 : List ℕ := [w0,w1,w2,w35,w37]

theorem h658 : Ban 60 5 v646 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v647 : List ℕ := [w0,w1,w2,w35,w37,w3]

theorem h659 : Ban 60 5 v647 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v648 : List ℕ := [w0,w1,w2,w35,w38,w3]

theorem h660 : Ban 60 5 v648 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v649 : List ℕ := [w0,w1,w2,w35,w39,w3]

theorem h661 : Ban 60 5 v649 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v650 : List ℕ := [w0,w1,w2,w35,w3,w41]

theorem h662 : Ban 60 5 v650 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v651 : List ℕ := [w0,w1,w2,w35,w3,w42]

theorem h663 : Ban 60 5 v651 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v652 : List ℕ := [w0,w1,w2,w35,w3,w60]

theorem h664 : Ban 60 5 v652 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v653 : List ℕ := [w0,w1,w2,w35,w3,w47]

theorem h665 : Ban 60 5 v653 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v654 : List ℕ := [w0,w1,w2,w35,w41]

theorem h666 : Ban 60 5 v654 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v655 : List ℕ := [w0,w1,w2,w35,w47]

theorem h667 : Ban 60 5 v655 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v656 : List ℕ := [w0,w1,w2,w160,w3]

theorem h668 : Ban 60 5 v656 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v657 : List ℕ := [w0,w1,w2,w3,w47]

theorem h669 : Ban 60 5 v657 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v658 : List ℕ := [w0,w1,w65,w35,w3]

theorem h670 : Ban 60 5 v658 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v659 : List ℕ := [w0,w1,w35,w160,w3]

theorem h671 : Ban 60 5 v659 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v660 : List ℕ := [w1,w2,w65,w35,w3]

theorem h672 : Ban 60 5 v660 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v661 : List ℕ := [w1,w2,w35,w3,w41]

theorem h673 : Ban 60 5 v661 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h633 : Ban 60 6 v621 := viaBranch (ws := [v622,v623,v624,v625,v626,v627,v628,v629,v39,v630,v91,v631,v632,v141,v633,v634,v230,v262,v292,v317,v371,v635,v636,v637,v638,v458,v639,v640,v507,v561,v641,v642,v643,v644,v645,v646,v647,v648,v649,v650,v651,v652,v653,v654,v655,v656,v657,v658,v659,v660,v661])
  (consBan h634 (consBan h635 (consBan h636 (consBan h637 (consBan h638 (consBan h639 (consBan h640 (consBan h641 (consBan h39 (consBan h642 (consBan h91 (consBan h643 (consBan h644 (consBan h141 (consBan h645 (consBan h646 (consBan h235 (consBan h267 (consBan h297 (consBan h322 (consBan h378 (consBan h647 (consBan h648 (consBan h649 (consBan h650 (consBan h465 (consBan h651 (consBan h652 (consBan h517 (consBan h573 (consBan h653 (consBan h654 (consBan h655 (consBan h656 (consBan h657 (consBan h658 (consBan h659 (consBan h660 (consBan h661 (consBan h662 (consBan h663 (consBan h664 (consBan h665 (consBan h666 (consBan h667 (consBan h668 (consBan h669 (consBan h670 (consBan h671 (consBan h672 (consBan h673 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v662 : List ℕ := [w0,w1,w2,w35,w3,w4]

theorem h674 : Ban 60 6 v662 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v663 : List ℕ := [w0,w1,w2,w36,w3,w4]

theorem h675 : Ban 60 6 v663 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v664 : List ℕ := [w0,w1,w2,w37,w3,w4]

theorem h676 : Ban 60 6 v664 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v665 : List ℕ := [w0,w1,w2,w37,w4]

def v666 : List ℕ := [w5,w0,w1,w2,w37,w4]

theorem h678 : Ban 60 5 v666 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v667 : List ℕ := [w9,w0,w1,w2,w37,w4]

theorem h679 : Ban 60 5 v667 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v668 : List ℕ := [w10,w0,w1,w2,w37,w4]

theorem h680 : Ban 60 5 v668 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v669 : List ℕ := [w14,w0,w1,w2,w37,w4]

theorem h681 : Ban 60 5 v669 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v670 : List ℕ := [w15,w0,w1,w2,w37,w4]

theorem h682 : Ban 60 5 v670 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v671 : List ℕ := [w16,w0,w1,w2,w37,w4]

theorem h683 : Ban 60 5 v671 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v672 : List ℕ := [w17,w0,w1,w2,w37,w4]

theorem h684 : Ban 60 5 v672 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v673 : List ℕ := [w18,w0,w1,w2,w37,w4]

theorem h685 : Ban 60 5 v673 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v674 : List ℕ := [w68,w0,w1,w2,w37,w4]

theorem h686 : Ban 60 5 v674 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v675 : List ℕ := [w24,w0,w1,w2,w37,w4]

theorem h687 : Ban 60 5 v675 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v676 : List ℕ := [w25,w0,w1,w2,w37,w4]

theorem h688 : Ban 60 5 v676 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v677 : List ℕ := [w26,w0,w1,w2,w37,w4]

theorem h689 : Ban 60 5 v677 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v678 : List ℕ := [w0,w1,w53,w2,w37,w4]

theorem h690 : Ban 60 5 v678 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v679 : List ℕ := [w0,w1,w54,w2,w37,w4]

theorem h691 : Ban 60 5 v679 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v680 : List ℕ := [w0,w1,w55,w2,w37,w4]

theorem h692 : Ban 60 5 v680 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v681 : List ℕ := [w0,w1,w56,w2,w37,w4]

theorem h693 : Ban 60 5 v681 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v682 : List ℕ := [w0,w1,w2,w35,w37,w4]

theorem h694 : Ban 60 5 v682 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v683 : List ℕ := [w0,w1,w2,w36,w37,w4]

theorem h695 : Ban 60 5 v683 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v684 : List ℕ := [w0,w1,w2,w106,w37,w4]

theorem h696 : Ban 60 5 v684 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v685 : List ℕ := [w0,w1,w2,w131,w37,w4]

theorem h697 : Ban 60 5 v685 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v686 : List ℕ := [w0,w1,w2,w37,w41,w4]

theorem h698 : Ban 60 5 v686 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w163 : ℕ := 0x942509425094250ffc00ffffffffff

def v687 : List ℕ := [w0,w1,w2,w37,w163,w4]

theorem h699 : Ban 60 5 v687 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v688 : List ℕ := [w0,w1,w2,w37,w59]

theorem h700 : Ban 60 5 v688 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v689 : List ℕ := [w0,w1,w2,w37,w59,w4]

theorem h701 : Ban 60 5 v689 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w164 : ℕ := 0xc6b1ac6b1ac6b1a00000ffc00fffff

def v690 : List ℕ := [w0,w1,w2,w37,w164,w4]

theorem h702 : Ban 60 5 v690 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v691 : List ℕ := [w0,w1,w2,w37,w43,w4]

theorem h703 : Ban 60 5 v691 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v692 : List ℕ := [w0,w1,w2,w37,w44,w4]

theorem h704 : Ban 60 5 v692 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v693 : List ℕ := [w0,w1,w2,w37,w4,w45]

theorem h705 : Ban 60 5 v693 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w165 : ℕ := 0xe4390e4390e4390fffffffc00003ff

def v694 : List ℕ := [w0,w1,w2,w37,w4,w165]

theorem h706 : Ban 60 5 v694 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v695 : List ℕ := [w0,w1,w2,w37,w4,w46]

theorem h707 : Ban 60 5 v695 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v696 : List ℕ := [w0,w1,w2,w37,w4,w48]

theorem h708 : Ban 60 5 v696 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v697 : List ℕ := [w0,w1,w2,w37,w45]

theorem h709 : Ban 60 5 v697 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v698 : List ℕ := [w0,w1,w2,w37,w165]

theorem h710 : Ban 60 5 v698 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v699 : List ℕ := [w0,w1,w2,w41,w4]

theorem h711 : Ban 60 5 v699 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v700 : List ℕ := [w0,w1,w2,w4,w165]

theorem h712 : Ban 60 5 v700 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v701 : List ℕ := [w0,w1,w65,w37,w4]

theorem h713 : Ban 60 5 v701 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v702 : List ℕ := [w0,w1,w37,w4,w45]

theorem h714 : Ban 60 5 v702 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v703 : List ℕ := [w1,w2,w37,w41,w4]

theorem h715 : Ban 60 5 v703 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h677 : Ban 60 6 v665 := viaBranch (ws := [v666,v667,v668,v669,v670,v671,v672,v673,v43,v674,v181,v675,v145,v676,v677,v231,v263,v293,v318,v372,v678,v679,v462,v680,v681,v508,v562,v646,v682,v683,v684,v685,v686,v687,v688,v689,v690,v691,v692,v693,v694,v695,v696,v697,v698,v699,v700,v701,v702,v526,v703])
  (consBan h678 (consBan h679 (consBan h680 (consBan h681 (consBan h682 (consBan h683 (consBan h684 (consBan h685 (consBan h43 (consBan h686 (consBan h181 (consBan h687 (consBan h145 (consBan h688 (consBan h689 (consBan h236 (consBan h268 (consBan h298 (consBan h323 (consBan h379 (consBan h690 (consBan h691 (consBan h469 (consBan h692 (consBan h693 (consBan h518 (consBan h574 (consBan h658 (consBan h694 (consBan h695 (consBan h696 (consBan h697 (consBan h698 (consBan h699 (consBan h700 (consBan h701 (consBan h702 (consBan h703 (consBan h704 (consBan h705 (consBan h706 (consBan h707 (consBan h708 (consBan h709 (consBan h710 (consBan h711 (consBan h712 (consBan h713 (consBan h714 (consBan h536 (consBan h715 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

theorem h716 : Ban 60 6 v248 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v704 : List ℕ := [w0,w1,w2,w39,w3,w4]

theorem h717 : Ban 60 6 v704 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v705 : List ℕ := [w0,w1,w2,w3,w41,w4]

def v706 : List ℕ := [w5,w0,w1,w2,w41,w4]

theorem h719 : Ban 60 5 v706 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v707 : List ℕ := [w10,w1,w2,w3,w41,w4]

theorem h720 : Ban 60 5 v707 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v708 : List ℕ := [w14,w0,w1,w2,w41,w4]

theorem h721 : Ban 60 5 v708 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v709 : List ℕ := [w114,w0,w1,w2,w3,w4]

theorem h722 : Ban 60 5 v709 := viaSmall (by decide +kernel) (by decide)

def v710 : List ℕ := [w15,w1,w2,w3,w41,w4]

theorem h723 : Ban 60 5 v710 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v711 : List ℕ := [w17,w1,w2,w3,w41,w4]

theorem h724 : Ban 60 5 v711 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w166 : ℕ := 0x200802008020080000000000003ff

def v712 : List ℕ := [w166,w0,w1,w2,w3,w4]

theorem h725 : Ban 60 5 v712 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

theorem h726 : Ban 60 5 v63 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v713 : List ℕ := [w22,w0,w1,w2,w41,w4]

theorem h727 : Ban 60 5 v713 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v714 : List ℕ := [w23,w0,w1,w2,w41,w4]

theorem h728 : Ban 60 5 v714 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v715 : List ℕ := [w23,w1,w2,w3,w41,w4]

theorem h729 : Ban 60 5 v715 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v716 : List ℕ := [w24,w1,w2,w3,w41,w4]

theorem h730 : Ban 60 5 v716 := viaSmall (by decide +kernel) (by decide)

def v717 : List ℕ := [w25,w1,w2,w3,w41,w4]

theorem h731 : Ban 60 5 v717 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v718 : List ℕ := [w26,w1,w2,w3,w41,w4]

theorem h732 : Ban 60 5 v718 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v719 : List ℕ := [w0,w28,w1,w2,w41,w4]

theorem h733 : Ban 60 5 v719 := viaSmall (by decide +kernel) (by decide)

def v720 : List ℕ := [w0,w116,w1,w2,w3,w4]

theorem h734 : Ban 60 5 v720 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v721 : List ℕ := [w0,w1,w124,w2,w3,w4]

theorem h735 : Ban 60 5 v721 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v722 : List ℕ := [w0,w1,w56,w2,w41,w4]

theorem h736 : Ban 60 5 v722 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v723 : List ℕ := [w0,w1,w2,w159,w3,w4]

theorem h737 : Ban 60 5 v723 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v724 : List ℕ := [w0,w1,w2,w35,w41,w4]

theorem h738 : Ban 60 5 v724 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v725 : List ℕ := [w0,w1,w2,w36,w41,w4]

theorem h739 : Ban 60 5 v725 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w167 : ℕ := 0x802008020080200003ff0000000000

def v726 : List ℕ := [w0,w1,w2,w167,w3,w4]

theorem h740 : Ban 60 5 v726 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

theorem h741 : Ban 60 5 v664 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v727 : List ℕ := [w0,w1,w2,w38,w41,w4]

theorem h742 : Ban 60 5 v727 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v728 : List ℕ := [w0,w1,w2,w39,w41,w4]

theorem h743 : Ban 60 5 v728 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def w168 : ℕ := 0x8d2348d2348d234003fffffff00000

def v729 : List ℕ := [w0,w1,w2,w3,w168,w4]

theorem h744 : Ban 60 5 v729 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v730 : List ℕ := [w0,w1,w2,w3,w118,w4]

theorem h745 : Ban 60 5 v730 := viaSmall (by decide +kernel) (by decide)

def v731 : List ℕ := [w0,w1,w2,w3,w41,w59]

theorem h746 : Ban 60 5 v731 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v732 : List ℕ := [w0,w1,w2,w3,w41,w45]

theorem h747 : Ban 60 5 v732 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v733 : List ℕ := [w0,w1,w2,w3,w41,w47]

theorem h748 : Ban 60 5 v733 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v734 : List ℕ := [w0,w1,w2,w3,w4,w117]

theorem h749 : Ban 60 5 v734 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v735 : List ℕ := [w0,w1,w2,w41,w42,w4]

theorem h750 : Ban 60 5 v735 := viaSmall (by decide +kernel) (by decide)

def v736 : List ℕ := [w0,w1,w2,w41,w60,w4]

theorem h751 : Ban 60 5 v736 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v737 : List ℕ := [w0,w1,w2,w41,w4,w47]

theorem h752 : Ban 60 5 v737 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v738 : List ℕ := [w0,w1,w65,w3,w41,w4]

theorem h753 : Ban 60 5 v738 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v739 : List ℕ := [w0,w1,w3,w41,w4,w45]

theorem h754 : Ban 60 5 v739 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v740 : List ℕ := [w1,w54,w2,w3,w41,w4]

theorem h755 : Ban 60 5 v740 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v741 : List ℕ := [w1,w2,w37,w3,w41,w4]

theorem h756 : Ban 60 5 v741 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v742 : List ℕ := [w1,w2,w3,w41,w44,w4]

theorem h757 : Ban 60 5 v742 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v743 : List ℕ := [w1,w2,w3,w41,w4,w46]

theorem h758 : Ban 60 5 v743 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h718 : Ban 60 6 v705 := viaBranch (ws := [v706,v707,v708,v709,v710,v711,v712,v47,v63,v713,v96,v109,v714,v715,v716,v717,v718,v719,v720,v256,v268,v721,v465,v722,v723,v650,v654,v724,v725,v726,v664,v686,v727,v728,v729,v730,v731,v732,v733,v389,v516,v734,v735,v736,v737,v738,v739,v310,v402,v740,v483,v527,v741,v703,v742,v743])
  (consBan h719 (consBan h720 (consBan h721 (consBan h722 (consBan h723 (consBan h724 (consBan h725 (consBan h47 (consBan h726 (consBan h727 (consBan h96 (consBan h109 (consBan h728 (consBan h729 (consBan h730 (consBan h731 (consBan h732 (consBan h733 (consBan h734 (consBan h261 (consBan h273 (consBan h735 (consBan h472 (consBan h736 (consBan h737 (consBan h662 (consBan h666 (consBan h738 (consBan h739 (consBan h740 (consBan h741 (consBan h698 (consBan h742 (consBan h743 (consBan h744 (consBan h745 (consBan h746 (consBan h747 (consBan h748 (consBan h396 (consBan h526 (consBan h749 (consBan h750 (consBan h751 (consBan h752 (consBan h753 (consBan h754 (consBan h315 (consBan h409 (consBan h755 (consBan h490 (consBan h537 (consBan h756 (consBan h715 (consBan h757 (consBan h758 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def w169 : ℕ := 0xfffff

def v744 : List ℕ := [w169,w0,w1,w2,w3,w4]

theorem h760 : Ban 60 5 v744 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v745 : List ℕ := [w169,w0,w1,w3,w42,w4]

theorem h761 : Ban 60 5 v745 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v746 : List ℕ := [w169,w0,w1,w3,w4]

theorem h762 : Ban 60 5 v746 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v747 : List ℕ := [w14,w0,w1,w2,w42,w4]

theorem h763 : Ban 60 5 v747 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v748 : List ℕ := [w14,w0,w2,w3,w42,w4]

theorem h764 : Ban 60 5 v748 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v749 : List ℕ := [w51,w0,w1,w2,w3,w4]

theorem h765 : Ban 60 5 v749 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w170 : ℕ := 0x8020080200802000000003ff00000

def v750 : List ℕ := [w170,w0,w1,w2,w3,w4]

theorem h766 : Ban 60 5 v750 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v751 : List ℕ := [w0,w28,w1,w2,w42,w4]

theorem h767 : Ban 60 5 v751 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

theorem h768 : Ban 60 5 v253 := viaSmall (by decide +kernel) (by decide)

def w171 : ℕ := 0x1c0701c0701c07000000ffffffffff

def v752 : List ℕ := [w0,w1,w171,w2,w3,w4]

theorem h769 : Ban 60 5 v752 := viaSmall (by decide +kernel) (by decide)

def w172 : ℕ := 0x4290a4290a4290a000000000000000

def v753 : List ℕ := [w0,w1,w172,w2,w3,w4]

theorem h770 : Ban 60 5 v753 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v754 : List ℕ := [w0,w1,w2,w158,w3,w4]

theorem h771 : Ban 60 5 v754 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w173 : ℕ := 0x802008020080200ffc000000000000

def v755 : List ℕ := [w0,w1,w2,w173,w3,w4]

theorem h772 : Ban 60 5 v755 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v756 : List ℕ := [w0,w1,w2,w37,w42,w4]

theorem h773 : Ban 60 5 v756 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v757 : List ℕ := [w0,w1,w2,w39,w42,w4]

theorem h774 : Ban 60 5 v757 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def w174 : ℕ := 0x942509425094250ffc00ffc00fffff

def v758 : List ℕ := [w0,w1,w2,w3,w174,w4]

theorem h775 : Ban 60 5 v758 := viaSmall (by decide +kernel) (by decide)

def v759 : List ℕ := [w0,w1,w2,w3,w113,w4]

theorem h776 : Ban 60 5 v759 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v760 : List ℕ := [w0,w1,w2,w3,w42,w59]

theorem h777 : Ban 60 5 v760 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v761 : List ℕ := [w0,w1,w2,w3,w42,w45]

theorem h778 : Ban 60 5 v761 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v762 : List ℕ := [w0,w1,w2,w3,w42,w47]

theorem h779 : Ban 60 5 v762 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def w175 : ℕ := 0xfc3f0fc3f0fc3f0fffffffffffffff

def v763 : List ℕ := [w0,w1,w2,w3,w4,w175]

theorem h780 : Ban 60 5 v763 := viaSmall (by decide +kernel) (by decide)

def v764 : List ℕ := [w0,w1,w2,w42,w60,w4]

theorem h781 : Ban 60 5 v764 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v765 : List ℕ := [w0,w1,w2,w42,w4,w47]

theorem h782 : Ban 60 5 v765 := viaSmall (by decide +kernel) (by decide)

def v766 : List ℕ := [w0,w1,w2,w42,w47]

def v767 : List ℕ := [w169,w0,w1,w42,w47]

theorem h784 : Ban 60 4 v767 := viaSmall (by decide +kernel) (by decide)

def w176 : ℕ := 0xffc00ffc0000000

def v768 : List ℕ := [w176,w0,w2,w42,w47]

theorem h785 : Ban 60 4 v768 := viaSmall (by decide +kernel) (by decide)

def v769 : List ℕ := [w24,w1,w2,w42,w47]

theorem h786 : Ban 60 4 v769 := viaSmall (by decide +kernel) (by decide)

def v770 : List ℕ := [w0,w31,w2,w42,w47]

theorem h787 : Ban 60 4 v770 := viaSmall (by decide +kernel) (by decide)

def v771 : List ℕ := [w0,w32,w2,w42,w47]

theorem h788 : Ban 60 4 v771 := viaSmall (by decide +kernel) (by decide)

def v772 : List ℕ := [w0,w1,w54,w42,w47]

theorem h789 : Ban 60 4 v772 := viaSmall (by decide +kernel) (by decide)

def v773 : List ℕ := [w0,w1,w2,w158,w47]

theorem h790 : Ban 60 4 v773 := viaSmall (by decide +kernel) (by decide)

def v774 : List ℕ := [w0,w1,w2,w38,w47]

theorem h791 : Ban 60 4 v774 := viaSmall (by decide +kernel) (by decide)

def w177 : ℕ := 0x8c2308c2308c230ffc00ffc00003ff

def v775 : List ℕ := [w0,w1,w2,w177,w47]

theorem h792 : Ban 60 4 v775 := viaSmall (by decide +kernel) (by decide)

def w178 : ℕ := 0xac2b0ac2b0ac2b0fffffffc0000000

def v776 : List ℕ := [w0,w1,w2,w42,w178]

theorem h793 : Ban 60 4 v776 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v777 : List ℕ := [w0,w1,w2,w42,w152]

theorem h794 : Ban 60 4 v777 := viaSmall (by decide +kernel) (by decide)

def v778 : List ℕ := [w0,w1,w65,w42,w47]

theorem h795 : Ban 60 4 v778 := viaSmall (by decide +kernel) (by decide)

def v779 : List ℕ := [w0,w1,w113,w42,w47]

theorem h796 : Ban 60 4 v779 := viaSmall (by decide +kernel) (by decide)

def v780 : List ℕ := [w0,w2,w58,w42,w47]

theorem h797 : Ban 60 4 v780 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v781 : List ℕ := [w0,w2,w38,w42,w47]

theorem h798 : Ban 60 4 v781 := viaSmall (by decide +kernel) (by decide)

def w179 : ℕ := 0xec3b0ec3b0ec3b0003ff00000003ff

def v782 : List ℕ := [w0,w2,w42,w179,w47]

theorem h799 : Ban 60 4 v782 := viaSmall (by decide +kernel) (by decide)

def v783 : List ℕ := [w1,w2,w65,w42,w47]

theorem h800 : Ban 60 4 v783 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h783 : Ban 60 5 v766 := viaBranch (ws := [v767,v768,v769,v770,v771,v772,v773,v774,v775,v776,v777,v778,v779,v380,v780,v781,v782,v783])
  (consBan h784 (consBan h785 (consBan h786 (consBan h787 (consBan h788 (consBan h789 (consBan h790 (consBan h791 (consBan h792 (consBan h793 (consBan h794 (consBan h795 (consBan h796 (consBan h387 (consBan h797 (consBan h798 (consBan h799 (consBan h800 (nilBan _ _)))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v784 : List ℕ := [w0,w1,w65,w3,w42,w4]

def w180 : ℕ := 0x8020080200802000000003fffffff

def v785 : List ℕ := [w180,w0,w1,w3,w4]

theorem h802 : Ban 60 4 v785 := viaSmall (by decide +kernel) (by decide)

def w181 : ℕ := 0x942509425094250ffc00ffc0000000

def v786 : List ℕ := [w0,w1,w3,w181,w4]

theorem h803 : Ban 60 4 v786 := viaSmall (by decide +kernel) (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h801 : Ban 60 5 v784 := viaBranch (ws := [v785,v778,v786,v399])
  (consBan h802 (consBan h795 (consBan h803 (consBan h406 (nilBan _ _)))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v787 : List ℕ := [w0,w1,w3,w113,w42,w4]

theorem h804 : Ban 60 5 v787 := viaSmall (by decide +kernel) (by decide)

def v788 : List ℕ := [w0,w1,w3,w113,w4]

def v789 : List ℕ := [w22,w1,w3,w113,w4]

theorem h806 : Ban 60 4 v789 := viaSmall (by decide +kernel) (by decide)

def v790 : List ℕ := [w0,w28,w1,w113,w4]

theorem h807 : Ban 60 4 v790 := viaSmall (by decide +kernel) (by decide)

def v791 : List ℕ := [w0,w29,w3,w113,w4]

theorem h808 : Ban 60 4 v791 := viaSmall (by decide +kernel) (by decide)

def v792 : List ℕ := [w0,w31,w3,w113,w4]

theorem h809 : Ban 60 4 v792 := viaSmall (by decide +kernel) (by decide)

def w182 : ℕ := 0x1c0701c0701c07000000fffff00000

def v793 : List ℕ := [w0,w1,w182,w3,w4]

theorem h810 : Ban 60 4 v793 := viaSmall (by decide +kernel) (by decide)

def v794 : List ℕ := [w0,w1,w35,w3,w113]

theorem h811 : Ban 60 4 v794 := viaSmall (by decide +kernel) (by decide)

def v795 : List ℕ := [w0,w1,w37,w113,w4]

theorem h812 : Ban 60 4 v795 := viaSmall (by decide +kernel) (by decide)

def v796 : List ℕ := [w0,w1,w3,w113,w47]

theorem h813 : Ban 60 4 v796 := viaSmall (by decide +kernel) (by decide)

def w183 : ℕ := 0x9f27c9f27c9f27cffffffffff00000

def v797 : List ℕ := [w0,w1,w3,w183,w4]

theorem h814 : Ban 60 4 v797 := viaSmall (by decide +kernel) (by decide)

def w184 : ℕ := 0xfc3f0fc3f0fc3f0ffffffffff00000

def v798 : List ℕ := [w0,w1,w3,w4,w184]

theorem h815 : Ban 60 4 v798 := viaSmall (by decide +kernel) (by decide)

def v799 : List ℕ := [w0,w1,w41,w113,w4]

theorem h816 : Ban 60 4 v799 := viaSmall (by decide +kernel) (by decide)

def v800 : List ℕ := [w0,w1,w113,w4,w47]

theorem h817 : Ban 60 4 v800 := viaSmall (by decide +kernel) (by decide)

def v801 : List ℕ := [w0,w3,w113,w4,w48]

theorem h818 : Ban 60 4 v801 := viaSmall (by decide +kernel) (by decide)

def v802 : List ℕ := [w1,w3,w41,w113,w4]

theorem h819 : Ban 60 4 v802 := viaSmall (by decide +kernel) (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h805 : Ban 60 5 v788 := viaBranch (ws := [v789,v790,v791,v792,v793,v794,v795,v786,v796,v797,v798,v799,v800,v398,v801,v802])
  (consBan h806 (consBan h807 (consBan h808 (consBan h809 (consBan h810 (consBan h811 (consBan h812 (consBan h803 (consBan h813 (consBan h814 (consBan h815 (consBan h816 (consBan h817 (consBan h405 (consBan h818 (consBan h819 (nilBan _ _)))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v803 : List ℕ := [w0,w1,w3,w42,w4,w45]

def w185 : ℕ := 0x802008020080200ffc0000000fffff

def v804 : List ℕ := [w0,w1,w185,w3,w4]

theorem h821 : Ban 60 4 v804 := viaSmall (by decide +kernel) (by decide)

def v805 : List ℕ := [w0,w3,w42,w45,w48]

theorem h822 : Ban 60 4 v805 := viaSmall (by decide +kernel) (by decide)

def v806 : List ℕ := [w1,w41,w42,w4,w45]

theorem h823 : Ban 60 4 v806 := viaSmall (by decide +kernel) (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h820 : Ban 60 5 v803 := viaBranch (ws := [v793,v804,v805,v806])
  (consBan h810 (consBan h821 (consBan h822 (consBan h823 (nilBan _ _)))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v807 : List ℕ := [w0,w2,w38,w3,w42,w4]

theorem h824 : Ban 60 5 v807 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v808 : List ℕ := [w0,w2,w3,w42,w4,w48]

def w186 : ℕ := 0x902409024090240ffc00fffffffc00

def v809 : List ℕ := [w0,w2,w3,w186,w4]

theorem h826 : Ban 60 4 v809 := viaSmall (by decide +kernel) (by decide)

def v810 : List ℕ := [w2,w3,w42,w4,w155]

theorem h827 : Ban 60 4 v810 := viaSmall (by decide +kernel) (by decide)

def v811 : List ℕ := [w2,w41,w42,w4,w48]

theorem h828 : Ban 60 4 v811 := viaSmall (by decide +kernel) (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h825 : Ban 60 5 v808 := viaBranch (ws := [v809,v801,v805,v810,v811])
  (consBan h826 (consBan h818 (consBan h822 (consBan h827 (consBan h828 (nilBan _ _))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v812 : List ℕ := [w1,w2,w65,w3,w42,w4]

theorem h829 : Ban 60 5 v812 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v813 : List ℕ := [w1,w2,w3,w41,w42,w4]

theorem h830 : Ban 60 5 v813 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v814 : List ℕ := [w1,w2,w41,w42,w4]

def v815 : List ℕ := [w169,w1,w41,w42,w4]

theorem h832 : Ban 60 4 v815 := viaSmall (by decide +kernel) (by decide)

def v816 : List ℕ := [w114,w2,w41,w42,w4]

theorem h833 : Ban 60 4 v816 := viaSmall (by decide +kernel) (by decide)

def v817 : List ℕ := [w18,w1,w41,w42,w4]

theorem h834 : Ban 60 4 v817 := viaSmall (by decide +kernel) (by decide)

def v818 : List ℕ := [w51,w1,w2,w41,w4]

theorem h835 : Ban 60 4 v818 := viaSmall (by decide +kernel) (by decide)

def v819 : List ℕ := [w29,w2,w41,w42,w4]

theorem h836 : Ban 60 4 v819 := viaSmall (by decide +kernel) (by decide)

def v820 : List ℕ := [w32,w2,w41,w42,w4]

theorem h837 : Ban 60 4 v820 := viaSmall (by decide +kernel) (by decide)

def v821 : List ℕ := [w1,w2,w38,w41,w4]

theorem h838 : Ban 60 4 v821 := viaSmall (by decide +kernel) (by decide)

def w187 : ℕ := 0x8c2308c2308c23000000fffff003ff

def v822 : List ℕ := [w1,w2,w187,w41,w4]

theorem h839 : Ban 60 4 v822 := viaSmall (by decide +kernel) (by decide)

def v823 : List ℕ := [w1,w2,w168,w42,w4]

theorem h840 : Ban 60 4 v823 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v824 : List ℕ := [w1,w2,w41,w42,w59]

theorem h841 : Ban 60 4 v824 := viaSmall (by decide +kernel) (by decide)

def v825 : List ℕ := [w1,w2,w41,w42,w45]

theorem h842 : Ban 60 4 v825 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v826 : List ℕ := [w1,w2,w42,w133,w4]

theorem h843 : Ban 60 4 v826 := viaSmall (by decide +kernel) (by decide)

def v827 : List ℕ := [w1,w41,w113,w42,w4]

theorem h844 : Ban 60 4 v827 := viaSmall (by decide +kernel) (by decide)

def v828 : List ℕ := [w2,w58,w41,w42,w4]

theorem h845 : Ban 60 4 v828 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v829 : List ℕ := [w2,w38,w41,w42,w4]

theorem h846 : Ban 60 4 v829 := viaSmall (by decide +kernel) (by decide)

def v830 : List ℕ := [w2,w118,w41,w42,w4]

theorem h847 : Ban 60 4 v830 := viaSmall (by decide +kernel) (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h831 : Ban 60 5 v814 := viaBranch (ws := [v815,v816,v817,v818,v819,v820,v821,v822,v823,v824,v825,v826,v827,v806,v828,v829,v830,v811])
  (consBan h832 (consBan h833 (consBan h834 (consBan h835 (consBan h836 (consBan h837 (consBan h838 (consBan h839 (consBan h840 (consBan h841 (consBan h842 (consBan h843 (consBan h844 (consBan h823 (consBan h845 (consBan h846 (consBan h847 (consBan h828 (nilBan _ _)))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h759 : Ban 60 6 v279 := viaBranch (ws := [v744,v745,v746,v747,v748,v48,v749,v97,v750,v149,v751,v243,v253,v269,v302,v330,v752,v466,v753,v754,v651,v755,v756,v248,v757,v758,v759,v760,v761,v762,v389,v575,v763,v735,v764,v765,v766,v784,v787,v788,v803,v396,v597,v807,v808,v812,v813,v814])
  (consBan h760 (consBan h761 (consBan h762 (consBan h763 (consBan h764 (consBan h48 (consBan h765 (consBan h97 (consBan h766 (consBan h149 (consBan h767 (consBan h248 (consBan h768 (consBan h274 (consBan h307 (consBan h335 (consBan h769 (consBan h473 (consBan h770 (consBan h771 (consBan h663 (consBan h772 (consBan h773 (consBan h253 (consBan h774 (consBan h775 (consBan h776 (consBan h777 (consBan h778 (consBan h779 (consBan h396 (consBan h587 (consBan h780 (consBan h750 (consBan h781 (consBan h782 (consBan h783 (consBan h801 (consBan h804 (consBan h805 (consBan h820 (consBan h403 (consBan h609 (consBan h824 (consBan h825 (consBan h829 (consBan h830 (consBan h831 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v831 : List ℕ := [w0,w1,w2,w3,w59]

def v832 : List ℕ := [w5,w0,w1,w2,w3,w59]

theorem h849 : Ban 60 5 v832 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v833 : List ℕ := [w9,w0,w1,w2,w3,w59]

theorem h850 : Ban 60 5 v833 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v834 : List ℕ := [w10,w0,w1,w2,w3,w59]

theorem h851 : Ban 60 5 v834 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v835 : List ℕ := [w14,w0,w1,w2,w3,w59]

theorem h852 : Ban 60 5 v835 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v836 : List ℕ := [w15,w0,w1,w2,w3,w59]

theorem h853 : Ban 60 5 v836 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v837 : List ℕ := [w16,w0,w1,w2,w3,w59]

theorem h854 : Ban 60 5 v837 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v838 : List ℕ := [w17,w0,w1,w2,w3,w59]

theorem h855 : Ban 60 5 v838 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v839 : List ℕ := [w22,w0,w1,w2,w3,w59]

theorem h856 : Ban 60 5 v839 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v840 : List ℕ := [w23,w0,w1,w2,w3,w59]

theorem h857 : Ban 60 5 v840 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v841 : List ℕ := [w24,w0,w1,w2,w3,w59]

theorem h858 : Ban 60 5 v841 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v842 : List ℕ := [w25,w0,w1,w2,w3,w59]

theorem h859 : Ban 60 5 v842 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v843 : List ℕ := [w26,w0,w1,w2,w3,w59]

theorem h860 : Ban 60 5 v843 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v844 : List ℕ := [w0,w28,w1,w2,w3,w59]

theorem h861 : Ban 60 5 v844 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v845 : List ℕ := [w0,w1,w157,w2,w3,w59]

theorem h862 : Ban 60 5 v845 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v846 : List ℕ := [w0,w1,w54,w2,w3,w59]

theorem h863 : Ban 60 5 v846 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v847 : List ℕ := [w0,w1,w55,w2,w3,w59]

theorem h864 : Ban 60 5 v847 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v848 : List ℕ := [w0,w1,w56,w2,w3,w59]

theorem h865 : Ban 60 5 v848 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v849 : List ℕ := [w0,w1,w2,w36,w3,w59]

theorem h866 : Ban 60 5 v849 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v850 : List ℕ := [w0,w1,w2,w37,w3,w59]

theorem h867 : Ban 60 5 v850 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v851 : List ℕ := [w0,w1,w2,w38,w3,w59]

theorem h868 : Ban 60 5 v851 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v852 : List ℕ := [w0,w1,w2,w39,w3,w59]

theorem h869 : Ban 60 5 v852 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v853 : List ℕ := [w0,w1,w2,w3,w146,w59]

theorem h870 : Ban 60 5 v853 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v854 : List ℕ := [w0,w1,w2,w3,w132,w59]

theorem h871 : Ban 60 5 v854 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w188 : ℕ := 0xab2acab2acab2acfffff003ff00000

def v855 : List ℕ := [w0,w1,w2,w3,w59,w188]

theorem h872 : Ban 60 5 v855 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w189 : ℕ := 0xac2b0ac2b0ac2b0fffffffc00003ff

def v856 : List ℕ := [w0,w1,w2,w3,w59,w189]

theorem h873 : Ban 60 5 v856 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w190 : ℕ := 0xb02c0b02c0b02c0ffffffffffffc00

def v857 : List ℕ := [w0,w1,w2,w3,w59,w190]

theorem h874 : Ban 60 5 v857 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v858 : List ℕ := [w0,w1,w2,w3,w59,w60]

theorem h875 : Ban 60 5 v858 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v859 : List ℕ := [w0,w1,w2,w3,w59,w45]

theorem h876 : Ban 60 5 v859 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v860 : List ℕ := [w0,w1,w2,w3,w189]

theorem h877 : Ban 60 5 v860 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v861 : List ℕ := [w0,w1,w2,w3,w45]

theorem h878 : Ban 60 5 v861 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v862 : List ℕ := [w0,w1,w2,w41,w59]

theorem h879 : Ban 60 5 v862 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v863 : List ℕ := [w0,w1,w2,w59,w189]

theorem h880 : Ban 60 5 v863 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v864 : List ℕ := [w0,w1,w3,w59,w45]

theorem h881 : Ban 60 5 v864 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v865 : List ℕ := [w1,w2,w65,w3,w59]

theorem h882 : Ban 60 5 v865 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v866 : List ℕ := [w1,w2,w3,w41,w59]

theorem h883 : Ban 60 5 v866 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h848 : Ban 60 6 v831 := viaBranch (ws := [v832,v833,v834,v835,v836,v837,v838,v839,v98,v840,v841,v150,v842,v843,v844,v203,v232,v265,v294,v319,v373,v636,v845,v846,v467,v847,v848,v509,v563,v849,v850,v688,v851,v852,v731,v760,v853,v854,v855,v856,v857,v858,v859,v860,v861,v862,v863,v520,v864,v865,v866])
  (consBan h849 (consBan h850 (consBan h851 (consBan h852 (consBan h853 (consBan h854 (consBan h855 (consBan h856 (consBan h98 (consBan h857 (consBan h858 (consBan h150 (consBan h859 (consBan h860 (consBan h861 (consBan h203 (consBan h237 (consBan h270 (consBan h299 (consBan h324 (consBan h380 (consBan h648 (consBan h862 (consBan h863 (consBan h474 (consBan h864 (consBan h865 (consBan h519 (consBan h575 (consBan h866 (consBan h867 (consBan h700 (consBan h868 (consBan h869 (consBan h746 (consBan h777 (consBan h870 (consBan h871 (consBan h872 (consBan h873 (consBan h874 (consBan h875 (consBan h876 (consBan h877 (consBan h878 (consBan h879 (consBan h880 (consBan h530 (consBan h881 (consBan h882 (consBan h883 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v867 : List ℕ := [w0,w1,w2,w3,w59,w4]

theorem h884 : Ban 60 6 v867 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v868 : List ℕ := [w0,w1,w2,w3,w60,w4]

theorem h885 : Ban 60 6 v868 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

theorem h886 : Ban 60 6 v280 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v869 : List ℕ := [w0,w1,w2,w3,w44,w4]

theorem h887 : Ban 60 6 v869 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v870 : List ℕ := [w0,w1,w2,w3,w4,w45]

def v871 : List ℕ := [w5,w0,w1,w3,w4,w45]

theorem h889 : Ban 60 5 v871 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v872 : List ℕ := [w9,w0,w1,w3,w4,w45]

theorem h890 : Ban 60 5 v872 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v873 : List ℕ := [w15,w0,w1,w2,w3,w45]

theorem h891 : Ban 60 5 v873 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v874 : List ℕ := [w16,w0,w1,w2,w3,w45]

theorem h892 : Ban 60 5 v874 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v875 : List ℕ := [w149,w0,w1,w2,w3,w4]

theorem h893 : Ban 60 5 v875 := viaSmall (by decide +kernel) (by decide)

def v876 : List ℕ := [w17,w0,w1,w3,w4,w45]

theorem h894 : Ban 60 5 v876 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w191 : ℕ := 0x20080200802008003ff0000000000

def v877 : List ℕ := [w191,w0,w1,w2,w3,w4]

theorem h895 : Ban 60 5 v877 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

theorem h896 : Ban 60 5 v10 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v878 : List ℕ := [w18,w0,w1,w2,w3,w45]

theorem h897 : Ban 60 5 v878 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v879 : List ℕ := [w62,w0,w1,w2,w3,w4]

theorem h898 : Ban 60 5 v879 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v880 : List ℕ := [w24,w0,w1,w3,w4,w45]

theorem h899 : Ban 60 5 v880 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v881 : List ℕ := [w25,w0,w1,w2,w3,w45]

theorem h900 : Ban 60 5 v881 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v882 : List ℕ := [w0,w70,w1,w2,w3,w4]

theorem h901 : Ban 60 5 v882 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v883 : List ℕ := [w0,w28,w1,w2,w3,w45]

theorem h902 : Ban 60 5 v883 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v884 : List ℕ := [w0,w1,w53,w2,w3,w45]

theorem h903 : Ban 60 5 v884 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v885 : List ℕ := [w0,w1,w53,w3,w4,w45]

theorem h904 : Ban 60 5 v885 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v886 : List ℕ := [w0,w1,w54,w3,w4,w45]

theorem h905 : Ban 60 5 v886 := viaSmall (by decide +kernel) (by decide)

def v887 : List ℕ := [w0,w1,w55,w3,w4,w45]

theorem h906 : Ban 60 5 v887 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v888 : List ℕ := [w0,w1,w56,w3,w4,w45]

theorem h907 : Ban 60 5 v888 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v889 : List ℕ := [w0,w1,w2,w35,w3,w45]

theorem h908 : Ban 60 5 v889 := viaSmall (by decide +kernel) (by decide)

def v890 : List ℕ := [w0,w1,w2,w151,w3,w4]

theorem h909 : Ban 60 5 v890 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v891 : List ℕ := [w0,w1,w2,w36,w3,w45]

theorem h910 : Ban 60 5 v891 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w192 : ℕ := 0x8020080200802000000000000003ff

def v892 : List ℕ := [w0,w1,w2,w192,w3,w4]

theorem h911 : Ban 60 5 v892 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

theorem h912 : Ban 60 5 v867 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v893 : List ℕ := [w0,w1,w2,w3,w43,w45]

theorem h913 : Ban 60 5 v893 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v894 : List ℕ := [w0,w1,w2,w3,w44,w45]

theorem h914 : Ban 60 5 v894 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w193 : ℕ := 0xe0b82e0b82e0b82ffc0000000fffff

def v895 : List ℕ := [w0,w1,w2,w3,w4,w193]

theorem h915 : Ban 60 5 v895 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v896 : List ℕ := [w0,w1,w2,w3,w4,w153]

theorem h916 : Ban 60 5 v896 := viaSmall (by decide +kernel) (by decide)

def v897 : List ℕ := [w0,w1,w2,w3,w4,w152]

theorem h917 : Ban 60 5 v897 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v898 : List ℕ := [w0,w1,w2,w3,w45,w46]

theorem h918 : Ban 60 5 v898 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v899 : List ℕ := [w0,w1,w2,w3,w45,w47]

theorem h919 : Ban 60 5 v899 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v900 : List ℕ := [w0,w1,w2,w3,w45,w48]

theorem h920 : Ban 60 5 v900 := viaSmall (by decide +kernel) (by decide)

def v901 : List ℕ := [w0,w1,w2,w41,w4,w45]

theorem h921 : Ban 60 5 v901 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v902 : List ℕ := [w0,w1,w2,w4,w45,w47]

theorem h922 : Ban 60 5 v902 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v903 : List ℕ := [w0,w1,w39,w3,w4,w45]

theorem h923 : Ban 60 5 v903 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v904 : List ℕ := [w0,w1,w3,w59,w4,w45]

theorem h924 : Ban 60 5 v904 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v905 : List ℕ := [w0,w1,w3,w60,w4,w45]

theorem h925 : Ban 60 5 v905 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v906 : List ℕ := [w1,w2,w65,w3,w4,w45]

theorem h926 : Ban 60 5 v906 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v907 : List ℕ := [w1,w2,w3,w41,w4,w45]

theorem h927 : Ban 60 5 v907 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h888 : Ban 60 6 v870 := viaBranch (ws := [v871,v872,v873,v874,v875,v876,v877,v10,v878,v51,v55,v103,v879,v880,v155,v164,v881,v882,v883,v207,v211,v225,v234,v327,v884,v885,v886,v887,v888,v889,v890,v891,v892,v693,v867,v859,v893,v894,v895,v896,v517,v897,v576,v898,v899,v900,v901,v902,v523,v578,v903,v904,v864,v905,v906,v907])
  (consBan h889 (consBan h890 (consBan h891 (consBan h892 (consBan h893 (consBan h894 (consBan h895 (consBan h896 (consBan h897 (consBan h51 (consBan h55 (consBan h103 (consBan h898 (consBan h899 (consBan h155 (consBan h164 (consBan h900 (consBan h901 (consBan h902 (consBan h207 (consBan h211 (consBan h230 (consBan h239 (consBan h332 (consBan h903 (consBan h904 (consBan h905 (consBan h906 (consBan h907 (consBan h908 (consBan h909 (consBan h910 (consBan h911 (consBan h705 (consBan h912 (consBan h876 (consBan h913 (consBan h914 (consBan h915 (consBan h916 (consBan h527 (consBan h917 (consBan h588 (consBan h918 (consBan h919 (consBan h920 (consBan h921 (consBan h922 (consBan h533 (consBan h590 (consBan h923 (consBan h924 (consBan h881 (consBan h925 (consBan h926 (consBan h927 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v908 : List ℕ := [w0,w1,w2,w3,w4,w46]

theorem h928 : Ban 60 6 v908 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v909 : List ℕ := [w0,w1,w2,w3,w4,w47]

def v910 : List ℕ := [w5,w0,w1,w2,w4,w47]

theorem h930 : Ban 60 5 v910 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v911 : List ℕ := [w14,w0,w1,w2,w4,w47]

theorem h931 : Ban 60 5 v911 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v912 : List ℕ := [w15,w0,w1,w2,w3,w47]

theorem h932 : Ban 60 5 v912 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v913 : List ℕ := [w16,w0,w1,w2,w3,w47]

theorem h933 : Ban 60 5 v913 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v914 : List ℕ := [w176,w0,w1,w2,w3,w4]

theorem h934 : Ban 60 5 v914 := viaSmall (by decide +kernel) (by decide)

def v915 : List ℕ := [w21,w0,w1,w2,w3,w4]

theorem h935 : Ban 60 5 v915 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v916 : List ℕ := [w18,w0,w1,w2,w3,w47]

theorem h936 : Ban 60 5 v916 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v917 : List ℕ := [w50,w0,w1,w2,w3,w4]

theorem h937 : Ban 60 5 v917 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v918 : List ℕ := [w22,w0,w1,w2,w4,w47]

theorem h938 : Ban 60 5 v918 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v919 : List ℕ := [w23,w0,w1,w2,w4,w47]

theorem h939 : Ban 60 5 v919 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w194 : ℕ := 0x80200802008020003ff0000000000

def v920 : List ℕ := [w194,w0,w1,w2,w3,w4]

theorem h940 : Ban 60 5 v920 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v921 : List ℕ := [w25,w0,w1,w2,w3,w47]

theorem h941 : Ban 60 5 v921 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

theorem h942 : Ban 60 5 v169 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v922 : List ℕ := [w0,w28,w1,w2,w3,w47]

theorem h943 : Ban 60 5 v922 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v923 : List ℕ := [w0,w1,w53,w2,w3,w47]

theorem h944 : Ban 60 5 v923 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w195 : ℕ := 0x4010040100401000000000000003ff

def v924 : List ℕ := [w0,w1,w195,w2,w3,w4]

theorem h945 : Ban 60 5 v924 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v925 : List ℕ := [w0,w1,w56,w2,w4,w47]

theorem h946 : Ban 60 5 v925 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

theorem h947 : Ban 60 5 v662 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v926 : List ℕ := [w0,w1,w2,w35,w4,w47]

theorem h948 : Ban 60 5 v926 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v927 : List ℕ := [w0,w1,w2,w36,w3,w47]

theorem h949 : Ban 60 5 v927 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v928 : List ℕ := [w0,w1,w2,w36,w4,w47]

theorem h950 : Ban 60 5 v928 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v929 : List ℕ := [w0,w1,w2,w37,w4,w47]

theorem h951 : Ban 60 5 v929 := viaSmall (by decide +kernel) (by decide)

def v930 : List ℕ := [w0,w1,w2,w38,w4,w47]

theorem h952 : Ban 60 5 v930 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v931 : List ℕ := [w0,w1,w2,w39,w4,w47]

theorem h953 : Ban 60 5 v931 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v932 : List ℕ := [w0,w1,w2,w3,w59,w47]

theorem h954 : Ban 60 5 v932 := viaSmall (by decide +kernel) (by decide)

def v933 : List ℕ := [w0,w1,w2,w3,w178,w4]

theorem h955 : Ban 60 5 v933 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v934 : List ℕ := [w0,w1,w2,w3,w43,w47]

theorem h956 : Ban 60 5 v934 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v935 : List ℕ := [w0,w1,w2,w3,w44,w47]

theorem h957 : Ban 60 5 v935 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w196 : ℕ := 0xe4390e4390e4390ffc00ffc00003ff

def v936 : List ℕ := [w0,w1,w2,w3,w4,w196]

theorem h958 : Ban 60 5 v936 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v937 : List ℕ := [w0,w1,w2,w3,w4,w179]

theorem h959 : Ban 60 5 v937 := viaSmall (by decide +kernel) (by decide)

def v938 : List ℕ := [w0,w1,w2,w3,w46,w47]

theorem h960 : Ban 60 5 v938 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v939 : List ℕ := [w0,w1,w2,w3,w47,w48]

theorem h961 : Ban 60 5 v939 := viaSmall (by decide +kernel) (by decide)

def v940 : List ℕ := [w0,w1,w2,w60,w4,w47]

theorem h962 : Ban 60 5 v940 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v941 : List ℕ := [w0,w1,w65,w3,w4,w47]

theorem h963 : Ban 60 5 v941 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v942 : List ℕ := [w0,w1,w3,w4,w45,w47]

theorem h964 : Ban 60 5 v942 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v943 : List ℕ := [w1,w2,w65,w3,w4,w47]

theorem h965 : Ban 60 5 v943 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v944 : List ℕ := [w1,w2,w3,w41,w4,w47]

theorem h966 : Ban 60 5 v944 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h929 : Ban 60 6 v909 := viaBranch (ws := [v910,v911,v912,v913,v914,v915,v916,v53,v56,v917,v918,v105,v110,v919,v920,v157,v921,v169,v922,v209,v212,v223,v235,v270,v923,v924,v474,v925,v662,v653,v926,v655,v927,v928,v929,v930,v931,v932,v933,v934,v935,v936,v937,v897,v734,v763,v899,v938,v939,v737,v765,v940,v941,v942,v943,v944])
  (consBan h930 (consBan h931 (consBan h932 (consBan h933 (consBan h934 (consBan h935 (consBan h936 (consBan h53 (consBan h56 (consBan h937 (consBan h938 (consBan h105 (consBan h110 (consBan h939 (consBan h940 (consBan h157 (consBan h941 (consBan h942 (consBan h943 (consBan h209 (consBan h212 (consBan h228 (consBan h240 (consBan h275 (consBan h944 (consBan h945 (consBan h481 (consBan h946 (consBan h947 (consBan h665 (consBan h948 (consBan h667 (consBan h949 (consBan h950 (consBan h951 (consBan h952 (consBan h953 (consBan h954 (consBan h955 (consBan h956 (consBan h957 (consBan h958 (consBan h959 (consBan h917 (consBan h749 (consBan h780 (consBan h919 (consBan h960 (consBan h961 (consBan h752 (consBan h782 (consBan h962 (consBan h963 (consBan h964 (consBan h965 (consBan h966 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def w197 : ℕ := 0x3ff003ff00000

def v945 : List ℕ := [w197,w0,w1,w2,w3,w4]

theorem h968 : Ban 60 5 v945 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v946 : List ℕ := [w197,w1,w2,w3,w4]

theorem h969 : Ban 60 5 v946 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v947 : List ℕ := [w197,w1,w2,w3,w4,w48]

theorem h970 : Ban 60 5 v947 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v948 : List ℕ := [w16,w0,w1,w2,w3,w48]

theorem h971 : Ban 60 5 v948 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v949 : List ℕ := [w16,w0,w2,w3,w4,w48]

theorem h972 : Ban 60 5 v949 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v950 : List ℕ := [w20,w0,w1,w2,w3,w4]

theorem h973 : Ban 60 5 v950 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def w198 : ℕ := 0xb02c0b02c0b02c000000000000000

def v951 : List ℕ := [w198,w0,w1,w2,w3,w4]

theorem h974 : Ban 60 5 v951 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v952 : List ℕ := [w0,w69,w1,w2,w3,w4]

theorem h975 : Ban 60 5 v952 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

theorem h976 : Ban 60 5 v219 := viaSmall (by decide +kernel) (by decide)

def w199 : ℕ := 0x4010040100401000000000000ffc00

def v953 : List ℕ := [w0,w1,w199,w2,w3,w4]

theorem h977 : Ban 60 5 v953 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v954 : List ℕ := [w0,w1,w2,w35,w3,w48]

theorem h978 : Ban 60 5 v954 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w200 : ℕ := 0x701c0701c0701c0fffff003ffffc00

def v955 : List ℕ := [w0,w1,w2,w200,w3,w4]

theorem h979 : Ban 60 5 v955 := viaSmall (by decide +kernel) (by decide)

def w201 : ℕ := 0x80200802008020000000ffc0000000

def v956 : List ℕ := [w0,w1,w2,w201,w3,w4]

theorem h980 : Ban 60 5 v956 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v957 : List ℕ := [w0,w1,w2,w3,w59,w48]

theorem h981 : Ban 60 5 v957 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w202 : ℕ := 0xb02c0b02c0b02c0ffffffffff00000

def v958 : List ℕ := [w0,w1,w2,w3,w202,w4]

theorem h982 : Ban 60 5 v958 := viaSmall (by decide +kernel) (by decide)

def v959 : List ℕ := [w0,w1,w2,w3,w44,w48]

theorem h983 : Ban 60 5 v959 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v960 : List ℕ := [w0,w1,w2,w3,w4,w155]

theorem h984 : Ban 60 5 v960 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v961 : List ℕ := [w0,w1,w2,w3,w46,w48]

theorem h985 : Ban 60 5 v961 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v962 : List ℕ := [w0,w1,w2,w41,w4,w48]

theorem h986 : Ban 60 5 v962 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v963 : List ℕ := [w0,w1,w2,w4,w47,w48]

theorem h987 : Ban 60 5 v963 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v964 : List ℕ := [w0,w1,w2,w47,w48]

def v965 : List ℕ := [w197,w1,w2,w47,w48]

theorem h989 : Ban 60 4 v965 := viaSmall (by decide +kernel) (by decide)

def v966 : List ℕ := [w176,w0,w2,w47,w48]

theorem h990 : Ban 60 4 v966 := viaSmall (by decide +kernel) (by decide)

def v967 : List ℕ := [w24,w1,w2,w47,w48]

theorem h991 : Ban 60 4 v967 := viaSmall (by decide +kernel) (by decide)

def v968 : List ℕ := [w0,w69,w1,w2,w47]

theorem h992 : Ban 60 4 v968 := viaSmall (by decide +kernel) (by decide)

def v969 : List ℕ := [w0,w31,w2,w47,w48]

theorem h993 : Ban 60 4 v969 := viaSmall (by decide +kernel) (by decide)

def v970 : List ℕ := [w0,w32,w2,w47,w48]

theorem h994 : Ban 60 4 v970 := viaSmall (by decide +kernel) (by decide)

def v971 : List ℕ := [w0,w1,w54,w47,w48]

theorem h995 : Ban 60 4 v971 := viaSmall (by decide +kernel) (by decide)

def v972 : List ℕ := [w0,w1,w2,w43,w47]

theorem h996 : Ban 60 4 v972 := viaSmall (by decide +kernel) (by decide)

def w203 : ℕ := 0xe0380e0380e0380fffffffc0000000

def v973 : List ℕ := [w0,w1,w2,w203,w47]

theorem h997 : Ban 60 4 v973 := viaSmall (by decide +kernel) (by decide)

def v974 : List ℕ := [w0,w1,w2,w196,w48]

theorem h998 : Ban 60 4 v974 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v975 : List ℕ := [w0,w1,w2,w117,w48]

theorem h999 : Ban 60 4 v975 := viaSmall (by decide +kernel) (by decide)

def v976 : List ℕ := [w0,w1,w65,w47,w48]

theorem h1000 : Ban 60 4 v976 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v977 : List ℕ := [w0,w34,w2,w47,w48]

theorem h1001 : Ban 60 4 v977 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v978 : List ℕ := [w0,w2,w43,w47,w48]

theorem h1002 : Ban 60 4 v978 := viaSmall (by decide +kernel) (by decide)

def v979 : List ℕ := [w0,w2,w179,w47,w48]

theorem h1003 : Ban 60 4 v979 := viaSmall (by decide +kernel) (by decide)

def v980 : List ℕ := [w1,w2,w65,w47,w48]

theorem h1004 : Ban 60 4 v980 := viaSmall (by decide +kernel) (by decide)

def v981 : List ℕ := [w1,w2,w47,w155,w48]

theorem h1005 : Ban 60 4 v981 := viaSmall (by decide +kernel) (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h988 : Ban 60 5 v964 := viaBranch (ws := [v965,v966,v967,v968,v969,v970,v971,v972,v973,v974,v975,v976,v977,v571,v978,v979,v980,v981])
  (consBan h989 (consBan h990 (consBan h991 (consBan h992 (consBan h993 (consBan h994 (consBan h995 (consBan h996 (consBan h997 (consBan h998 (consBan h999 (consBan h1000 (consBan h1001 (consBan h583 (consBan h1002 (consBan h1003 (consBan h1004 (consBan h1005 (nilBan _ _)))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v982 : List ℕ := [w0,w1,w65,w3,w4,w48]

theorem h1006 : Ban 60 5 v982 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v983 : List ℕ := [w0,w1,w3,w4,w45,w48]

theorem h1007 : Ban 60 5 v983 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v984 : List ℕ := [w0,w1,w3,w45,w48]

def v985 : List ℕ := [w197,w1,w3,w45,w48]

theorem h1009 : Ban 60 4 v985 := viaSmall (by decide +kernel) (by decide)

def v986 : List ℕ := [w149,w0,w3,w45,w48]

theorem h1010 : Ban 60 4 v986 := viaSmall (by decide +kernel) (by decide)

def v987 : List ℕ := [w20,w0,w1,w3,w45]

theorem h1011 : Ban 60 4 v987 := viaSmall (by decide +kernel) (by decide)

def v988 : List ℕ := [w22,w1,w3,w45,w48]

theorem h1012 : Ban 60 4 v988 := viaSmall (by decide +kernel) (by decide)

def v989 : List ℕ := [w0,w30,w3,w45,w48]

theorem h1013 : Ban 60 4 v989 := viaSmall (by decide +kernel) (by decide)

def v990 : List ℕ := [w0,w31,w3,w45,w48]

theorem h1014 : Ban 60 4 v990 := viaSmall (by decide +kernel) (by decide)

def v991 : List ℕ := [w0,w1,w37,w45,w48]

theorem h1015 : Ban 60 4 v991 := viaSmall (by decide +kernel) (by decide)

def v992 : List ℕ := [w0,w1,w3,w43,w45]

theorem h1016 : Ban 60 4 v992 := viaSmall (by decide +kernel) (by decide)

def w204 : ℕ := 0xe0380e0380e0380fffff00000ffc00

def v993 : List ℕ := [w0,w1,w3,w204,w45]

theorem h1017 : Ban 60 4 v993 := viaSmall (by decide +kernel) (by decide)

def v994 : List ℕ := [w0,w1,w3,w193,w48]

theorem h1018 : Ban 60 4 v994 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v995 : List ℕ := [w0,w1,w3,w122,w48]

theorem h1019 : Ban 60 4 v995 := viaSmall (by decide +kernel) (by decide)

def v996 : List ℕ := [w0,w1,w41,w45,w48]

theorem h1020 : Ban 60 4 v996 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v997 : List ℕ := [w0,w34,w3,w45,w48]

theorem h1021 : Ban 60 4 v997 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v998 : List ℕ := [w0,w3,w43,w45,w48]

theorem h1022 : Ban 60 4 v998 := viaSmall (by decide +kernel) (by decide)

def v999 : List ℕ := [w0,w3,w153,w45,w48]

theorem h1023 : Ban 60 4 v999 := viaSmall (by decide +kernel) (by decide)

def v1000 : List ℕ := [w1,w3,w41,w45,w48]

theorem h1024 : Ban 60 4 v1000 := viaSmall (by decide +kernel) (by decide)

def v1001 : List ℕ := [w1,w3,w45,w155,w48]

theorem h1025 : Ban 60 4 v1001 := viaSmall (by decide +kernel) (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h1008 : Ban 60 5 v984 := viaBranch (ws := [v985,v986,v987,v988,v989,v990,v991,v992,v993,v994,v995,v996,v997,v805,v998,v999,v1000,v1001])
  (consBan h1009 (consBan h1010 (consBan h1011 (consBan h1012 (consBan h1013 (consBan h1014 (consBan h1015 (consBan h1016 (consBan h1017 (consBan h1018 (consBan h1019 (consBan h1020 (consBan h1021 (consBan h822 (consBan h1022 (consBan h1023 (consBan h1024 (consBan h1025 (nilBan _ _)))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v1002 : List ℕ := [w0,w2,w3,w43,w4,w48]

theorem h1026 : Ban 60 5 v1002 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1003 : List ℕ := [w1,w2,w65,w3,w4,w48]

def w205 : ℕ := 0x401004010040100003ff003ffffc00

def v1004 : List ℕ := [w1,w205,w2,w3,w4]

theorem h1028 : Ban 60 4 v1004 := viaSmall (by decide +kernel) (by decide)

def w206 : ℕ := 0xb02c0b02c0b02c0ffc00ffc0000000

def v1005 : List ℕ := [w1,w2,w3,w206,w4]

theorem h1029 : Ban 60 4 v1005 := viaSmall (by decide +kernel) (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h1027 : Ban 60 5 v1003 := viaBranch (ws := [v1004,v980,v1005,v601])
  (consBan h1028 (consBan h1004 (consBan h1029 (consBan h613 (nilBan _ _)))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v1006 : List ℕ := [w1,w2,w3,w41,w4,w48]

def w207 : ℕ := 0x701c0701c0701c0ffc0000000ffc00

def v1007 : List ℕ := [w1,w2,w207,w3,w4]

theorem h1031 : Ban 60 4 v1007 := viaSmall (by decide +kernel) (by decide)

def w208 : ℕ := 0x802008020080200003fffffff00000

def v1008 : List ℕ := [w1,w2,w208,w3,w4]

theorem h1032 : Ban 60 4 v1008 := viaSmall (by decide +kernel) (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h1030 : Ban 60 5 v1006 := viaBranch (ws := [v1007,v1008,v1000,v811])
  (consBan h1031 (consBan h1032 (consBan h1024 (consBan h828 (nilBan _ _)))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v1009 : List ℕ := [w1,w2,w3,w4,w155]

def v1010 : List ℕ := [w18,w1,w3,w4,w155]

theorem h1034 : Ban 60 4 v1010 := viaSmall (by decide +kernel) (by decide)

def v1011 : List ℕ := [w28,w1,w2,w4,w155]

theorem h1035 : Ban 60 4 v1011 := viaSmall (by decide +kernel) (by decide)

def v1012 : List ℕ := [w30,w2,w3,w4,w155]

theorem h1036 : Ban 60 4 v1012 := viaSmall (by decide +kernel) (by decide)

def v1013 : List ℕ := [w32,w2,w3,w4,w155]

theorem h1037 : Ban 60 4 v1013 := viaSmall (by decide +kernel) (by decide)

def v1014 : List ℕ := [w1,w2,w35,w3,w155]

theorem h1038 : Ban 60 4 v1014 := viaSmall (by decide +kernel) (by decide)

def v1015 : List ℕ := [w1,w2,w3,w59,w155]

theorem h1039 : Ban 60 4 v1015 := viaSmall (by decide +kernel) (by decide)

def w209 : ℕ := 0xf2bcaf2bcaf2bcaffc00ffc00fffff

def v1016 : List ℕ := [w1,w2,w3,w4,w209]

theorem h1040 : Ban 60 4 v1016 := viaSmall (by decide +kernel) (by decide)

def w210 : ℕ := 0xfc3f0fc3f0fc3f0ffc00ffc00fffff

def v1017 : List ℕ := [w1,w2,w3,w4,w210]

theorem h1041 : Ban 60 4 v1017 := viaSmall (by decide +kernel) (by decide)

def v1018 : List ℕ := [w1,w2,w3,w45,w155]

theorem h1042 : Ban 60 4 v1018 := viaSmall (by decide +kernel) (by decide)

def v1019 : List ℕ := [w1,w2,w3,w47,w155]

theorem h1043 : Ban 60 4 v1019 := viaSmall (by decide +kernel) (by decide)

def v1020 : List ℕ := [w1,w2,w4,w47,w155]

theorem h1044 : Ban 60 4 v1020 := viaSmall (by decide +kernel) (by decide)

def v1021 : List ℕ := [w1,w3,w4,w45,w155]

theorem h1045 : Ban 60 4 v1021 := viaSmall (by decide +kernel) (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h1033 : Ban 60 5 v1009 := viaBranch (ws := [v1010,v1011,v1012,v1013,v1014,v1007,v1015,v1005,v1016,v1017,v1018,v1019,v1020,v1021,v600,v810])
  (consBan h1034 (consBan h1035 (consBan h1036 (consBan h1037 (consBan h1038 (consBan h1031 (consBan h1039 (consBan h1029 (consBan h1040 (consBan h1041 (consBan h1042 (consBan h1043 (consBan h1044 (consBan h1045 (consBan h612 (consBan h827 (nilBan _ _)))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v1022 : List ℕ := [w1,w2,w3,w4,w155,w48]

theorem h1046 : Ban 60 5 v1022 := viaSmall (by decide +kernel) (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h967 : Ban 60 6 v250 := viaBranch (ws := [v945,v946,v947,v948,v949,v950,v54,v106,v158,v951,v952,v210,v219,v236,v276,v303,v331,v953,v475,v954,v955,v956,v696,v957,v958,v280,v959,v960,v576,v391,v763,v900,v961,v939,v962,v963,v964,v982,v983,v984,v400,v598,v808,v1002,v1003,v1006,v1009,v1022])
  (consBan h968 (consBan h969 (consBan h970 (consBan h971 (consBan h972 (consBan h973 (consBan h54 (consBan h106 (consBan h158 (consBan h974 (consBan h975 (consBan h210 (consBan h976 (consBan h241 (consBan h281 (consBan h308 (consBan h336 (consBan h977 (consBan h482 (consBan h978 (consBan h979 (consBan h980 (consBan h708 (consBan h981 (consBan h982 (consBan h285 (consBan h983 (consBan h984 (consBan h588 (consBan h398 (consBan h780 (consBan h920 (consBan h985 (consBan h961 (consBan h986 (consBan h987 (consBan h988 (consBan h1006 (consBan h1007 (consBan h1008 (consBan h407 (consBan h610 (consBan h825 (consBan h1026 (consBan h1027 (consBan h1030 (consBan h1033 (consBan h1046 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v1023 : List ℕ := [w5,w0,w1,w2,w3,w45]

theorem h1048 : Ban 60 5 v1023 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1024 : List ℕ := [w9,w0,w1,w2,w3,w45]

theorem h1049 : Ban 60 5 v1024 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1025 : List ℕ := [w10,w0,w1,w2,w3,w45]

theorem h1050 : Ban 60 5 v1025 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1026 : List ℕ := [w14,w0,w1,w2,w3,w45]

theorem h1051 : Ban 60 5 v1026 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1027 : List ℕ := [w149,w0,w1,w2,w3,w45]

theorem h1052 : Ban 60 5 v1027 := viaSmall (by decide +kernel) (by decide)

def v1028 : List ℕ := [w17,w0,w1,w2,w3,w45]

theorem h1053 : Ban 60 5 v1028 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1029 : List ℕ := [w191,w0,w1,w2,w3,w45]

theorem h1054 : Ban 60 5 v1029 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1030 : List ℕ := [w22,w0,w1,w2,w3,w45]

theorem h1055 : Ban 60 5 v1030 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1031 : List ℕ := [w23,w0,w1,w2,w3,w45]

theorem h1056 : Ban 60 5 v1031 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1032 : List ℕ := [w62,w0,w1,w2,w3,w45]

theorem h1057 : Ban 60 5 v1032 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1033 : List ℕ := [w24,w0,w1,w2,w3,w45]

theorem h1058 : Ban 60 5 v1033 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1034 : List ℕ := [w26,w0,w1,w2,w3,w45]

theorem h1059 : Ban 60 5 v1034 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1035 : List ℕ := [w0,w70,w1,w2,w3,w45]

theorem h1060 : Ban 60 5 v1035 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1036 : List ℕ := [w0,w76,w1,w2,w3,w45]

theorem h1061 : Ban 60 5 v1036 := viaSmall (by decide +kernel) (by decide)

def v1037 : List ℕ := [w0,w1,w54,w2,w3,w45]

theorem h1062 : Ban 60 5 v1037 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1038 : List ℕ := [w0,w1,w55,w2,w3,w45]

theorem h1063 : Ban 60 5 v1038 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

theorem h1064 : Ban 60 5 v585 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1039 : List ℕ := [w0,w1,w56,w2,w3,w45]

theorem h1065 : Ban 60 5 v1039 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1040 : List ℕ := [w0,w1,w2,w151,w3]

theorem h1066 : Ban 60 5 v1040 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1041 : List ℕ := [w0,w1,w2,w151,w3,w45]

theorem h1067 : Ban 60 5 v1041 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1042 : List ℕ := [w0,w1,w2,w192,w3,w45]

theorem h1068 : Ban 60 5 v1042 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1043 : List ℕ := [w0,w1,w2,w37,w3,w45]

theorem h1069 : Ban 60 5 v1043 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1044 : List ℕ := [w0,w1,w2,w38,w3,w45]

theorem h1070 : Ban 60 5 v1044 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1045 : List ℕ := [w0,w1,w2,w39,w3,w45]

theorem h1071 : Ban 60 5 v1045 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

theorem h1072 : Ban 60 5 v831 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1046 : List ℕ := [w0,w1,w2,w3,w60,w45]

theorem h1073 : Ban 60 5 v1046 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1047 : List ℕ := [w0,w1,w2,w3,w193,w45]

theorem h1074 : Ban 60 5 v1047 := viaSmall (by decide +kernel) (by decide)

def v1048 : List ℕ := [w0,w1,w2,w3,w153,w45]

theorem h1075 : Ban 60 5 v1048 := viaSmall (by decide +kernel) (by decide)

def v1049 : List ℕ := [w0,w1,w2,w3,w45,w122]

theorem h1076 : Ban 60 5 v1049 := viaSmall (by decide +kernel) (by decide)

def v1050 : List ℕ := [w0,w1,w2,w3,w45,w152]

theorem h1077 : Ban 60 5 v1050 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1051 : List ℕ := [w0,w1,w2,w3,w45,w148]

theorem h1078 : Ban 60 5 v1051 := viaSmall (by decide +kernel) (by decide)

def v1052 : List ℕ := [w0,w1,w2,w3,w152]

theorem h1079 : Ban 60 5 v1052 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1053 : List ℕ := [w0,w1,w2,w41,w45]

def v1054 : List ℕ := [w166,w0,w1,w41,w45]

theorem h1081 : Ban 60 4 v1054 := viaSmall (by decide +kernel) (by decide)

def v1055 : List ℕ := [w191,w1,w2,w41,w45]

theorem h1082 : Ban 60 4 v1055 := viaSmall (by decide +kernel) (by decide)

def v1056 : List ℕ := [w26,w1,w2,w41,w45]

theorem h1083 : Ban 60 4 v1056 := viaSmall (by decide +kernel) (by decide)

def v1057 : List ℕ := [w0,w1,w55,w41,w45]

theorem h1084 : Ban 60 4 v1057 := viaSmall (by decide +kernel) (by decide)

theorem h1085 : Ban 60 4 v697 := viaSmall (by decide +kernel) (by decide)

theorem h1086 : Ban 60 4 v862 := viaSmall (by decide +kernel) (by decide)

def v1058 : List ℕ := [w0,w1,w168,w41,w45]

theorem h1087 : Ban 60 4 v1058 := viaSmall (by decide +kernel) (by decide)

def v1059 : List ℕ := [w0,w1,w41,w59,w45]

theorem h1088 : Ban 60 4 v1059 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1060 : List ℕ := [w1,w2,w37,w41,w45]

theorem h1089 : Ban 60 4 v1060 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1061 : List ℕ := [w1,w2,w41,w193,w45]

theorem h1090 : Ban 60 4 v1061 := viaSmall (by decide +kernel) (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h1080 : Ban 60 5 v1053 := viaBranch (ws := [v1054,v1055,v1056,v1057,v697,v862,v568,v1058,v1059,v377,v1060,v1061])
  (consBan h1081 (consBan h1082 (consBan h1083 (consBan h1084 (consBan h1085 (consBan h1086 (consBan h580 (consBan h1087 (consBan h1088 (consBan h384 (consBan h1089 (consBan h1090 (nilBan _ _)))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v1062 : List ℕ := [w1,w2,w65,w3,w45]

theorem h1091 : Ban 60 5 v1062 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1063 : List ℕ := [w1,w2,w3,w41,w45]

theorem h1092 : Ban 60 5 v1063 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h1047 : Ban 60 6 v861 := viaBranch (ws := [v1023,v1024,v1025,v1026,v1027,v1028,v1029,v1030,v107,v1031,v1032,v1033,v159,v1034,v1035,v1036,v266,v295,v320,v374,v1037,v1038,v585,v1039,v510,v564,v1040,v1041,v1042,v1043,v697,v1044,v1045,v732,v761,v831,v859,v1046,v1047,v1048,v1049,v1050,v1051,v1052,v1053,v579,v864,v1062,v1063])
  (consBan h1048 (consBan h1049 (consBan h1050 (consBan h1051 (consBan h1052 (consBan h1053 (consBan h1054 (consBan h1055 (consBan h107 (consBan h1056 (consBan h1057 (consBan h1058 (consBan h159 (consBan h1059 (consBan h1060 (consBan h1061 (consBan h271 (consBan h300 (consBan h325 (consBan h381 (consBan h1062 (consBan h1063 (consBan h1064 (consBan h1065 (consBan h520 (consBan h576 (consBan h1066 (consBan h1067 (consBan h1068 (consBan h1069 (consBan h709 (consBan h1070 (consBan h1071 (consBan h747 (consBan h778 (consBan h1072 (consBan h876 (consBan h1073 (consBan h1074 (consBan h1075 (consBan h1076 (consBan h1077 (consBan h1078 (consBan h1079 (consBan h1080 (consBan h591 (consBan h881 (consBan h1091 (consBan h1092 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v1064 : List ℕ := [w5,w0,w1,w2,w3,w47]

theorem h1094 : Ban 60 5 v1064 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1065 : List ℕ := [w9,w0,w1,w2,w3,w47]

theorem h1095 : Ban 60 5 v1065 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1066 : List ℕ := [w10,w0,w1,w2,w3,w47]

theorem h1096 : Ban 60 5 v1066 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1067 : List ℕ := [w14,w0,w1,w2,w3,w47]

theorem h1097 : Ban 60 5 v1067 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1068 : List ℕ := [w176,w0,w1,w2,w3,w47]

theorem h1098 : Ban 60 5 v1068 := viaSmall (by decide +kernel) (by decide)

def v1069 : List ℕ := [w17,w0,w1,w2,w3,w47]

theorem h1099 : Ban 60 5 v1069 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1070 : List ℕ := [w21,w0,w1,w2,w3,w47]

theorem h1100 : Ban 60 5 v1070 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1071 : List ℕ := [w50,w0,w1,w2,w3,w47]

theorem h1101 : Ban 60 5 v1071 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1072 : List ℕ := [w22,w0,w1,w2,w3,w47]

theorem h1102 : Ban 60 5 v1072 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1073 : List ℕ := [w23,w0,w1,w2,w3,w47]

theorem h1103 : Ban 60 5 v1073 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1074 : List ℕ := [w194,w0,w1,w2,w3,w47]

theorem h1104 : Ban 60 5 v1074 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1075 : List ℕ := [w24,w0,w1,w2,w3,w47]

theorem h1105 : Ban 60 5 v1075 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1076 : List ℕ := [w26,w0,w1,w2,w3,w47]

theorem h1106 : Ban 60 5 v1076 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1077 : List ℕ := [w0,w74,w1,w2,w3,w47]

theorem h1107 : Ban 60 5 v1077 := viaSmall (by decide +kernel) (by decide)

def v1078 : List ℕ := [w0,w1,w195,w2,w3,w47]

theorem h1108 : Ban 60 5 v1078 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1079 : List ℕ := [w0,w1,w54,w2,w3,w47]

theorem h1109 : Ban 60 5 v1079 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1080 : List ℕ := [w0,w1,w55,w2,w3,w47]

theorem h1110 : Ban 60 5 v1080 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1081 : List ℕ := [w0,w1,w56,w2,w3,w47]

theorem h1111 : Ban 60 5 v1081 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

theorem h1112 : Ban 60 5 v621 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1082 : List ℕ := [w0,w1,w2,w37,w3,w47]

theorem h1113 : Ban 60 5 v1082 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1083 : List ℕ := [w0,w1,w2,w38,w3,w47]

theorem h1114 : Ban 60 5 v1083 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

theorem h1115 : Ban 60 5 v774 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1084 : List ℕ := [w0,w1,w2,w39,w3,w47]

theorem h1116 : Ban 60 5 v1084 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1085 : List ℕ := [w0,w1,w2,w3,w178]

theorem h1117 : Ban 60 5 v1085 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1086 : List ℕ := [w0,w1,w2,w3,w178,w47]

theorem h1118 : Ban 60 5 v1086 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1087 : List ℕ := [w0,w1,w2,w3,w60,w47]

theorem h1119 : Ban 60 5 v1087 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1088 : List ℕ := [w0,w1,w2,w3,w196,w47]

theorem h1120 : Ban 60 5 v1088 := viaSmall (by decide +kernel) (by decide)

def v1089 : List ℕ := [w0,w1,w2,w3,w179,w47]

theorem h1121 : Ban 60 5 v1089 := viaSmall (by decide +kernel) (by decide)

def v1090 : List ℕ := [w0,w1,w2,w3,w47,w152]

theorem h1122 : Ban 60 5 v1090 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1091 : List ℕ := [w0,w1,w2,w3,w47,w117]

theorem h1123 : Ban 60 5 v1091 := viaSmall (by decide +kernel) (by decide)

def v1092 : List ℕ := [w0,w1,w2,w3,w47,w175]

theorem h1124 : Ban 60 5 v1092 := viaSmall (by decide +kernel) (by decide)

def v1093 : List ℕ := [w0,w1,w65,w3,w47]

def v1094 : List ℕ := [w128,w0,w1,w65,w47]

theorem h1126 : Ban 60 4 v1094 := viaSmall (by decide +kernel) (by decide)

def v1095 : List ℕ := [w194,w1,w65,w3,w47]

theorem h1127 : Ban 60 4 v1095 := viaSmall (by decide +kernel) (by decide)

def v1096 : List ℕ := [w26,w1,w65,w3,w47]

theorem h1128 : Ban 60 4 v1096 := viaSmall (by decide +kernel) (by decide)

theorem h1129 : Ban 60 4 v477 := viaSmall (by decide +kernel) (by decide)

def v1097 : List ℕ := [w0,w1,w130,w65,w47]

theorem h1130 : Ban 60 4 v1097 := viaSmall (by decide +kernel) (by decide)

theorem h1131 : Ban 60 4 v658 := viaSmall (by decide +kernel) (by decide)

def v1098 : List ℕ := [w0,w1,w65,w35,w47]

theorem h1132 : Ban 60 4 v1098 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1099 : List ℕ := [w0,w1,w65,w38,w47]

theorem h1133 : Ban 60 4 v1099 := viaSmall (by decide +kernel) (by decide)

def v1100 : List ℕ := [w1,w54,w65,w3,w47]

theorem h1134 : Ban 60 4 v1100 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1101 : List ℕ := [w1,w65,w3,w196,w47]

theorem h1135 : Ban 60 4 v1101 := viaSmall (by decide +kernel) (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h1125 : Ban 60 5 v1093 := viaBranch (ws := [v1094,v1095,v1096,v477,v1097,v658,v1098,v1099,v778,v381,v1100,v1101])
  (consBan h1126 (consBan h1127 (consBan h1128 (consBan h1129 (consBan h1130 (consBan h1131 (consBan h1132 (consBan h1133 (consBan h795 (consBan h388 (consBan h1134 (consBan h1135 (nilBan _ _)))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v1102 : List ℕ := [w1,w2,w65,w3,w47]

theorem h1136 : Ban 60 5 v1102 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1103 : List ℕ := [w1,w2,w3,w41,w47]

theorem h1137 : Ban 60 5 v1103 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h1093 : Ban 60 6 v657 := viaBranch (ws := [v1064,v1065,v1066,v1067,v1068,v1069,v1070,v1071,v1072,v108,v1073,v1074,v1075,v160,v1076,v1077,v267,v296,v321,v378,v1078,v1079,v477,v1080,v1081,v511,v565,v621,v653,v655,v1082,v1083,v774,v1084,v733,v762,v1085,v1086,v1087,v1088,v1089,v1090,v1091,v1092,v1052,v766,v1093,v1102,v1103])
  (consBan h1094 (consBan h1095 (consBan h1096 (consBan h1097 (consBan h1098 (consBan h1099 (consBan h1100 (consBan h1101 (consBan h1102 (consBan h108 (consBan h1103 (consBan h1104 (consBan h1105 (consBan h160 (consBan h1106 (consBan h1107 (consBan h272 (consBan h301 (consBan h326 (consBan h385 (consBan h1108 (consBan h1109 (consBan h484 (consBan h1110 (consBan h1111 (consBan h521 (consBan h577 (consBan h1112 (consBan h665 (consBan h667 (consBan h1113 (consBan h1114 (consBan h1115 (consBan h1116 (consBan h748 (consBan h779 (consBan h1117 (consBan h1118 (consBan h1119 (consBan h1120 (consBan h1121 (consBan h1122 (consBan h1123 (consBan h1124 (consBan h1079 (consBan h783 (consBan h1125 (consBan h1136 (consBan h1137 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v1104 : List ℕ := [w9,w0,w1,w2,w41,w4]

theorem h1139 : Ban 60 5 v1104 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1105 : List ℕ := [w10,w0,w1,w2,w41,w4]

theorem h1140 : Ban 60 5 v1105 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1106 : List ℕ := [w114,w0,w1,w2,w41,w4]

theorem h1141 : Ban 60 5 v1106 := viaSmall (by decide +kernel) (by decide)

def v1107 : List ℕ := [w15,w0,w1,w2,w41,w4]

theorem h1142 : Ban 60 5 v1107 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1108 : List ℕ := [w16,w0,w1,w2,w41,w4]

theorem h1143 : Ban 60 5 v1108 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1109 : List ℕ := [w17,w0,w1,w2,w41,w4]

theorem h1144 : Ban 60 5 v1109 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1110 : List ℕ := [w166,w0,w1,w2,w41,w4]

theorem h1145 : Ban 60 5 v1110 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1111 : List ℕ := [w18,w0,w1,w2,w41,w4]

theorem h1146 : Ban 60 5 v1111 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1112 : List ℕ := [w24,w0,w1,w2,w41,w4]

theorem h1147 : Ban 60 5 v1112 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1113 : List ℕ := [w25,w0,w1,w2,w41,w4]

theorem h1148 : Ban 60 5 v1113 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1114 : List ℕ := [w26,w0,w1,w2,w41,w4]

theorem h1149 : Ban 60 5 v1114 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

theorem h1150 : Ban 60 5 v408 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1115 : List ℕ := [w0,w116,w1,w2,w41,w4]

theorem h1151 : Ban 60 5 v1115 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1116 : List ℕ := [w0,w116,w1,w2,w4]

theorem h1152 : Ban 60 5 v1116 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1117 : List ℕ := [w0,w80,w1,w2,w41,w4]

theorem h1153 : Ban 60 5 v1117 := viaSmall (by decide +kernel) (by decide)

def v1118 : List ℕ := [w0,w1,w53,w2,w41,w4]

theorem h1154 : Ban 60 5 v1118 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1119 : List ℕ := [w0,w1,w124,w2,w41,w4]

theorem h1155 : Ban 60 5 v1119 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1120 : List ℕ := [w0,w1,w54,w2,w41,w4]

theorem h1156 : Ban 60 5 v1120 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1121 : List ℕ := [w0,w1,w55,w2,w41,w4]

theorem h1157 : Ban 60 5 v1121 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1122 : List ℕ := [w0,w1,w2,w159,w41,w4]

theorem h1158 : Ban 60 5 v1122 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1123 : List ℕ := [w0,w1,w2,w167,w41,w4]

theorem h1159 : Ban 60 5 v1123 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

theorem h1160 : Ban 60 5 v665 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1124 : List ℕ := [w0,w1,w2,w168,w41,w4]

theorem h1161 : Ban 60 5 v1124 := viaSmall (by decide +kernel) (by decide)

def v1125 : List ℕ := [w0,w1,w2,w118,w41,w4]

theorem h1162 : Ban 60 5 v1125 := viaSmall (by decide +kernel) (by decide)

def v1126 : List ℕ := [w0,w1,w2,w41,w107,w4]

theorem h1163 : Ban 60 5 v1126 := viaSmall (by decide +kernel) (by decide)

def v1127 : List ℕ := [w0,w1,w2,w41,w59,w4]

theorem h1164 : Ban 60 5 v1127 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1128 : List ℕ := [w0,w1,w2,w41,w133,w4]

theorem h1165 : Ban 60 5 v1128 := viaSmall (by decide +kernel) (by decide)

def v1129 : List ℕ := [w0,w1,w2,w41,w43,w4]

theorem h1166 : Ban 60 5 v1129 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1130 : List ℕ := [w0,w1,w2,w41,w44,w4]

theorem h1167 : Ban 60 5 v1130 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1131 : List ℕ := [w0,w1,w2,w41,w4,w46]

theorem h1168 : Ban 60 5 v1131 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1132 : List ℕ := [w0,w1,w2,w41,w4,w117]

theorem h1169 : Ban 60 5 v1132 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1133 : List ℕ := [w0,w1,w2,w4,w117]

theorem h1170 : Ban 60 5 v1133 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1134 : List ℕ := [w0,w1,w65,w41,w4]

theorem h1171 : Ban 60 5 v1134 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1135 : List ℕ := [w0,w1,w41,w4,w45]

theorem h1172 : Ban 60 5 v1135 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h1138 : Ban 60 6 v699 := viaBranch (ws := [v1104,v1105,v1106,v1107,v1108,v1109,v1110,v1111,v57,v1112,v1113,v1114,v408,v1115,v1116,v237,v1117,v297,v322,v382,v1118,v1119,v1120,v478,v1121,v512,v566,v1122,v1123,v686,v665,v1124,v1125,v1126,v862,v1127,v1128,v1129,v1130,v901,v1131,v1132,v962,v1053,v1133,v1134,v1135,v404,v703])
  (consBan h1139 (consBan h1140 (consBan h1141 (consBan h1142 (consBan h1143 (consBan h1144 (consBan h1145 (consBan h1146 (consBan h57 (consBan h1147 (consBan h1148 (consBan h1149 (consBan h1150 (consBan h1151 (consBan h1152 (consBan h242 (consBan h1153 (consBan h302 (consBan h327 (consBan h389 (consBan h1154 (consBan h1155 (consBan h1156 (consBan h485 (consBan h1157 (consBan h522 (consBan h578 (consBan h1158 (consBan h1159 (consBan h698 (consBan h1160 (consBan h1161 (consBan h1162 (consBan h1163 (consBan h879 (consBan h1164 (consBan h1165 (consBan h1166 (consBan h1167 (consBan h921 (consBan h1168 (consBan h1169 (consBan h986 (consBan h1080 (consBan h1170 (consBan h1171 (consBan h1172 (consBan h411 (consBan h715 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v1136 : List ℕ := [w9,w0,w1,w2,w4,w47]

theorem h1174 : Ban 60 5 v1136 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1137 : List ℕ := [w10,w0,w1,w2,w4,w47]

theorem h1175 : Ban 60 5 v1137 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1138 : List ℕ := [w15,w0,w1,w2,w4,w47]

theorem h1176 : Ban 60 5 v1138 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1139 : List ℕ := [w16,w0,w1,w2,w4,w47]

theorem h1177 : Ban 60 5 v1139 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1140 : List ℕ := [w176,w0,w1,w2,w4,w47]

theorem h1178 : Ban 60 5 v1140 := viaSmall (by decide +kernel) (by decide)

def v1141 : List ℕ := [w17,w0,w1,w2,w4,w47]

theorem h1179 : Ban 60 5 v1141 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1142 : List ℕ := [w21,w0,w1,w2,w4,w47]

theorem h1180 : Ban 60 5 v1142 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1143 : List ℕ := [w18,w0,w1,w2,w4,w47]

theorem h1181 : Ban 60 5 v1143 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1144 : List ℕ := [w50,w0,w1,w2,w4,w47]

theorem h1182 : Ban 60 5 v1144 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1145 : List ℕ := [w194,w0,w1,w2,w4,w47]

theorem h1183 : Ban 60 5 v1145 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1146 : List ℕ := [w24,w0,w1,w2,w4,w47]

theorem h1184 : Ban 60 5 v1146 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1147 : List ℕ := [w25,w0,w1,w2,w4,w47]

theorem h1185 : Ban 60 5 v1147 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1148 : List ℕ := [w26,w0,w1,w2,w4,w47]

theorem h1186 : Ban 60 5 v1148 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

theorem h1187 : Ban 60 5 v170 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1149 : List ℕ := [w0,w74,w1,w2,w4,w47]

theorem h1188 : Ban 60 5 v1149 := viaSmall (by decide +kernel) (by decide)

def v1150 : List ℕ := [w0,w1,w53,w2,w4,w47]

theorem h1189 : Ban 60 5 v1150 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1151 : List ℕ := [w0,w1,w195,w2,w4,w47]

theorem h1190 : Ban 60 5 v1151 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1152 : List ℕ := [w0,w1,w54,w2,w4,w47]

theorem h1191 : Ban 60 5 v1152 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1153 : List ℕ := [w0,w1,w55,w2,w4,w47]

theorem h1192 : Ban 60 5 v1153 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1154 : List ℕ := [w0,w1,w2,w59,w4,w47]

theorem h1193 : Ban 60 5 v1154 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1155 : List ℕ := [w0,w1,w2,w178,w4,w47]

theorem h1194 : Ban 60 5 v1155 := viaSmall (by decide +kernel) (by decide)

def v1156 : List ℕ := [w0,w1,w2,w43,w4,w47]

theorem h1195 : Ban 60 5 v1156 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

theorem h1196 : Ban 60 5 v972 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1157 : List ℕ := [w0,w1,w2,w44,w4,w47]

theorem h1197 : Ban 60 5 v1157 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1158 : List ℕ := [w0,w1,w2,w4,w196]

theorem h1198 : Ban 60 5 v1158 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1159 : List ℕ := [w0,w1,w2,w4,w196,w47]

theorem h1199 : Ban 60 5 v1159 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1160 : List ℕ := [w0,w1,w2,w4,w46,w47]

theorem h1200 : Ban 60 5 v1160 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1161 : List ℕ := [w0,w1,w2,w4,w179,w47]

theorem h1201 : Ban 60 5 v1161 := viaSmall (by decide +kernel) (by decide)

def v1162 : List ℕ := [w0,w1,w2,w4,w47,w152]

theorem h1202 : Ban 60 5 v1162 := viaSmall (by decide +kernel) (by decide)

def v1163 : List ℕ := [w0,w1,w2,w4,w47,w117]

theorem h1203 : Ban 60 5 v1163 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1164 : List ℕ := [w0,w1,w2,w4,w47,w175]

theorem h1204 : Ban 60 5 v1164 := viaSmall (by decide +kernel) (by decide)

def v1165 : List ℕ := [w0,w1,w65,w4,w47]

theorem h1205 : Ban 60 5 v1165 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1166 : List ℕ := [w0,w1,w4,w45,w47]

theorem h1206 : Ban 60 5 v1166 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1167 : List ℕ := [w1,w2,w65,w4,w47]

theorem h1208 : Ban 60 4 v162 := viaSmall (by decide +kernel) (by decide)

def v1168 : List ℕ := [w24,w1,w65,w4,w47]

theorem h1209 : Ban 60 4 v1168 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1169 : List ℕ := [w121,w1,w2,w65,w47]

theorem h1210 : Ban 60 4 v1169 := viaSmall (by decide +kernel) (by decide)

theorem h1211 : Ban 60 4 v218 := viaSmall (by decide +kernel) (by decide)

def v1170 : List ℕ := [w28,w1,w2,w65,w47]

theorem h1212 : Ban 60 4 v1170 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1171 : List ℕ := [w1,w195,w65,w4,w47]

theorem h1213 : Ban 60 4 v1171 := viaSmall (by decide +kernel) (by decide)

def v1172 : List ℕ := [w1,w129,w2,w65,w47]

theorem h1214 : Ban 60 4 v1172 := viaSmall (by decide +kernel) (by decide)

def v1173 : List ℕ := [w1,w55,w65,w4,w47]

theorem h1215 : Ban 60 4 v1173 := viaSmall (by decide +kernel) (by decide)

def v1174 : List ℕ := [w1,w2,w65,w43,w47]

theorem h1216 : Ban 60 4 v1174 := viaSmall (by decide +kernel) (by decide)

def v1175 : List ℕ := [w1,w65,w178,w4,w47]

theorem h1217 : Ban 60 4 v1175 := viaSmall (by decide +kernel) (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h1207 : Ban 60 5 v1167 := viaBranch (ws := [v162,v1168,v1169,v218,v1170,v1171,v1172,v1173,v1174,v980,v572,v1175])
  (consBan h1208 (consBan h1209 (consBan h1210 (consBan h1211 (consBan h1212 (consBan h1213 (consBan h1214 (consBan h1215 (consBan h1216 (consBan h1004 (consBan h584 (consBan h1217 (nilBan _ _)))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h1173 : Ban 60 6 v216 := viaBranch (ws := [v1136,v1137,v1138,v1139,v1140,v1141,v1142,v1143,v58,v1144,v1145,v1146,v162,v1147,v1148,v170,v209,v212,v1149,v238,v298,v323,v383,v1150,v1151,v1152,v479,v1153,v513,v569,v1154,v1155,v1156,v972,v1157,v902,v1158,v1159,v1160,v1161,v1162,v1163,v963,v1164,v1133,v964,v1165,v1166,v1167])
  (consBan h1174 (consBan h1175 (consBan h1176 (consBan h1177 (consBan h1178 (consBan h1179 (consBan h1180 (consBan h1181 (consBan h58 (consBan h1182 (consBan h1183 (consBan h1184 (consBan h162 (consBan h1185 (consBan h1186 (consBan h1187 (consBan h209 (consBan h212 (consBan h1188 (consBan h243 (consBan h303 (consBan h328 (consBan h390 (consBan h1189 (consBan h1190 (consBan h1191 (consBan h486 (consBan h1192 (consBan h523 (consBan h581 (consBan h1193 (consBan h1194 (consBan h1195 (consBan h1196 (consBan h1197 (consBan h922 (consBan h1198 (consBan h1199 (consBan h1200 (consBan h1201 (consBan h1202 (consBan h1203 (consBan h987 (consBan h1204 (consBan h1170 (consBan h988 (consBan h1205 (consBan h1206 (consBan h1207 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v1176 : List ℕ := [w10,w0,w1,w65,w3,w4]

theorem h1219 : Ban 60 5 v1176 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1177 : List ℕ := [w119,w0,w1,w65,w3,w4]

theorem h1220 : Ban 60 5 v1177 := viaSmall (by decide +kernel) (by decide)

def v1178 : List ℕ := [w14,w0,w1,w65,w3,w4]

theorem h1221 : Ban 60 5 v1178 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1179 : List ℕ := [w15,w0,w1,w65,w3,w4]

theorem h1222 : Ban 60 5 v1179 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1180 : List ℕ := [w16,w0,w1,w65,w3,w4]

theorem h1223 : Ban 60 5 v1180 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1181 : List ℕ := [w22,w0,w1,w65,w3,w4]

theorem h1224 : Ban 60 5 v1181 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1182 : List ℕ := [w23,w0,w1,w65,w3,w4]

theorem h1225 : Ban 60 5 v1182 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1183 : List ℕ := [w128,w0,w1,w65,w3,w4]

theorem h1226 : Ban 60 5 v1183 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1184 : List ℕ := [w25,w0,w1,w65,w3,w4]

theorem h1227 : Ban 60 5 v1184 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1185 : List ℕ := [w26,w0,w1,w65,w3,w4]

theorem h1228 : Ban 60 5 v1185 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

theorem h1229 : Ban 60 5 v424 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1186 : List ℕ := [w0,w121,w1,w65,w3,w4]

theorem h1230 : Ban 60 5 v1186 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1187 : List ℕ := [w0,w121,w1,w3,w4]

theorem h1231 : Ban 60 5 v1187 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1188 : List ℕ := [w0,w28,w1,w65,w3,w4]

theorem h1232 : Ban 60 5 v1188 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1189 : List ℕ := [w0,w85,w1,w65,w3,w4]

theorem h1233 : Ban 60 5 v1189 := viaSmall (by decide +kernel) (by decide)

def v1190 : List ℕ := [w0,w1,w129,w65,w3,w4]

theorem h1234 : Ban 60 5 v1190 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

theorem h1235 : Ban 60 5 v440 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1191 : List ℕ := [w0,w1,w130,w65,w3,w4]

theorem h1236 : Ban 60 5 v1191 := viaSmall (by decide +kernel) (by decide)

def v1192 : List ℕ := [w0,w1,w123,w65,w3,w4]

theorem h1237 : Ban 60 5 v1192 := viaSmall (by decide +kernel) (by decide)

def v1193 : List ℕ := [w0,w1,w65,w105,w3,w4]

theorem h1238 : Ban 60 5 v1193 := viaSmall (by decide +kernel) (by decide)

def v1194 : List ℕ := [w0,w1,w65,w35,w3,w4]

theorem h1239 : Ban 60 5 v1194 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1195 : List ℕ := [w0,w1,w65,w36,w3,w4]

theorem h1240 : Ban 60 5 v1195 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1196 : List ℕ := [w0,w1,w65,w131,w3,w4]

theorem h1241 : Ban 60 5 v1196 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1197 : List ℕ := [w0,w1,w65,w37,w3,w4]

theorem h1242 : Ban 60 5 v1197 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1198 : List ℕ := [w0,w1,w65,w38,w3,w4]

theorem h1243 : Ban 60 5 v1198 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1199 : List ℕ := [w0,w1,w65,w3,w132,w4]

theorem h1244 : Ban 60 5 v1199 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1200 : List ℕ := [w0,w1,w65,w3,w133,w4]

theorem h1245 : Ban 60 5 v1200 := viaSmall (by decide +kernel) (by decide)

def v1201 : List ℕ := [w0,w1,w65,w3,w43,w4]

theorem h1246 : Ban 60 5 v1201 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1202 : List ℕ := [w0,w1,w65,w3,w44,w4]

theorem h1247 : Ban 60 5 v1202 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1203 : List ℕ := [w0,w1,w65,w3,w4,w46]

theorem h1248 : Ban 60 5 v1203 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1204 : List ℕ := [w0,w1,w65,w3,w4,w122]

theorem h1249 : Ban 60 5 v1204 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1205 : List ℕ := [w0,w1,w3,w4,w122]

theorem h1250 : Ban 60 5 v1205 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h1218 : Ban 60 6 v480 := viaBranch (ws := [v1176,v1177,v1178,v1179,v1180,v1181,v1182,v1183,v1184,v1185,v424,v1186,v1187,v1188,v213,v239,v271,v1189,v299,v384,v1190,v456,v440,v1191,v1192,v1193,v658,v1194,v1195,v1196,v1197,v701,v1198,v738,v784,v1199,v1200,v1201,v1202,v1203,v1204,v941,v982,v1093,v1134,v1165,v1205,v421,v482])
  (consBan h1219 (consBan h1220 (consBan h1221 (consBan h1222 (consBan h1223 (consBan h1224 (consBan h1225 (consBan h1226 (consBan h1227 (consBan h1228 (consBan h1229 (consBan h1230 (consBan h1231 (consBan h1232 (consBan h213 (consBan h244 (consBan h276 (consBan h1233 (consBan h304 (consBan h391 (consBan h1234 (consBan h463 (consBan h1235 (consBan h1236 (consBan h1237 (consBan h1238 (consBan h670 (consBan h1239 (consBan h1240 (consBan h1241 (consBan h1242 (consBan h713 (consBan h1243 (consBan h753 (consBan h801 (consBan h1244 (consBan h1245 (consBan h1246 (consBan h1247 (consBan h1248 (consBan h1249 (consBan h963 (consBan h1006 (consBan h1125 (consBan h1171 (consBan h1205 (consBan h1250 (consBan h428 (consBan h489 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v1206 : List ℕ := [w10,w0,w1,w3,w4,w45]

theorem h1252 : Ban 60 5 v1206 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1207 : List ℕ := [w14,w0,w1,w3,w4,w45]

theorem h1253 : Ban 60 5 v1207 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1208 : List ℕ := [w15,w0,w1,w3,w4,w45]

theorem h1254 : Ban 60 5 v1208 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1209 : List ℕ := [w16,w0,w1,w3,w4,w45]

theorem h1255 : Ban 60 5 v1209 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1210 : List ℕ := [w149,w0,w1,w3,w4,w45]

theorem h1256 : Ban 60 5 v1210 := viaSmall (by decide +kernel) (by decide)

def v1211 : List ℕ := [w191,w0,w1,w3,w4,w45]

theorem h1257 : Ban 60 5 v1211 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

theorem h1258 : Ban 60 5 v11 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1212 : List ℕ := [w22,w0,w1,w3,w4,w45]

theorem h1259 : Ban 60 5 v1212 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1213 : List ℕ := [w23,w0,w1,w3,w4,w45]

theorem h1260 : Ban 60 5 v1213 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1214 : List ℕ := [w62,w0,w1,w3,w4,w45]

theorem h1261 : Ban 60 5 v1214 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1215 : List ℕ := [w25,w0,w1,w3,w4,w45]

theorem h1262 : Ban 60 5 v1215 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1216 : List ℕ := [w26,w0,w1,w3,w4,w45]

theorem h1263 : Ban 60 5 v1216 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1217 : List ℕ := [w0,w70,w1,w3,w4,w45]

theorem h1264 : Ban 60 5 v1217 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1218 : List ℕ := [w0,w28,w1,w3,w4,w45]

theorem h1265 : Ban 60 5 v1218 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1219 : List ℕ := [w0,w76,w1,w3,w4,w45]

theorem h1266 : Ban 60 5 v1219 := viaSmall (by decide +kernel) (by decide)

def v1220 : List ℕ := [w0,w1,w35,w3,w4,w45]

theorem h1267 : Ban 60 5 v1220 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1221 : List ℕ := [w0,w1,w151,w3,w4,w45]

theorem h1268 : Ban 60 5 v1221 := viaSmall (by decide +kernel) (by decide)

def v1222 : List ℕ := [w0,w1,w36,w3,w4,w45]

theorem h1269 : Ban 60 5 v1222 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1223 : List ℕ := [w0,w1,w192,w3,w4,w45]

theorem h1270 : Ban 60 5 v1223 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1224 : List ℕ := [w0,w1,w37,w3,w4,w45]

theorem h1271 : Ban 60 5 v1224 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1225 : List ℕ := [w0,w1,w38,w3,w4,w45]

theorem h1272 : Ban 60 5 v1225 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1226 : List ℕ := [w0,w1,w3,w43,w4,w45]

theorem h1273 : Ban 60 5 v1226 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

theorem h1274 : Ban 60 5 v992 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1227 : List ℕ := [w0,w1,w3,w44,w4,w45]

theorem h1275 : Ban 60 5 v1227 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1228 : List ℕ := [w0,w1,w3,w4,w193]

theorem h1276 : Ban 60 5 v1228 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1229 : List ℕ := [w0,w1,w3,w4,w193,w45]

theorem h1277 : Ban 60 5 v1229 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1230 : List ℕ := [w0,w1,w3,w4,w153,w45]

theorem h1278 : Ban 60 5 v1230 := viaSmall (by decide +kernel) (by decide)

def v1231 : List ℕ := [w0,w1,w3,w4,w45,w46]

theorem h1279 : Ban 60 5 v1231 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1232 : List ℕ := [w0,w1,w3,w4,w45,w122]

theorem h1280 : Ban 60 5 v1232 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1233 : List ℕ := [w0,w1,w3,w4,w45,w152]

theorem h1281 : Ban 60 5 v1233 := viaSmall (by decide +kernel) (by decide)

def v1234 : List ℕ := [w0,w1,w3,w4,w45,w148]

theorem h1282 : Ban 60 5 v1234 := viaSmall (by decide +kernel) (by decide)

def v1235 : List ℕ := [w1,w3,w41,w4,w45]

theorem h1284 : Ban 60 4 v60 := viaSmall (by decide +kernel) (by decide)

def v1236 : List ℕ := [w18,w1,w3,w41,w45]

theorem h1285 : Ban 60 4 v1236 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

theorem h1286 : Ban 60 4 v112 := viaSmall (by decide +kernel) (by decide)

def v1237 : List ℕ := [w22,w1,w41,w4,w45]

theorem h1287 : Ban 60 4 v1237 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1238 : List ℕ := [w116,w1,w3,w41,w45]

theorem h1288 : Ban 60 4 v1238 := viaSmall (by decide +kernel) (by decide)

def v1239 : List ℕ := [w1,w151,w41,w4,w45]

theorem h1289 : Ban 60 4 v1239 := viaSmall (by decide +kernel) (by decide)

def v1240 : List ℕ := [w1,w192,w41,w4,w45]

theorem h1290 : Ban 60 4 v1240 := viaSmall (by decide +kernel) (by decide)

def v1241 : List ℕ := [w1,w167,w3,w41,w45]

theorem h1291 : Ban 60 4 v1241 := viaSmall (by decide +kernel) (by decide)

def v1242 : List ℕ := [w1,w38,w41,w4,w45]

theorem h1292 : Ban 60 4 v1242 := viaSmall (by decide +kernel) (by decide)

def v1243 : List ℕ := [w1,w3,w41,w43,w45]

theorem h1293 : Ban 60 4 v1243 := viaSmall (by decide +kernel) (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h1283 : Ban 60 5 v1235 := viaBranch (ws := [v60,v1236,v112,v1237,v1238,v1239,v1240,v1241,v1242,v1243,v1000,v806])
  (consBan h1284 (consBan h1285 (consBan h1286 (consBan h1287 (consBan h1288 (consBan h1289 (consBan h1290 (consBan h1291 (consBan h1292 (consBan h1293 (consBan h1024 (consBan h823 (nilBan _ _)))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h1251 : Ban 60 6 v62 := viaBranch (ws := [v1206,v1207,v1208,v1209,v1210,v1211,v11,v51,v55,v1212,v112,v1213,v1214,v1215,v1216,v1217,v1218,v214,v1219,v240,v272,v300,v385,v1220,v1221,v1222,v1223,v1224,v702,v1225,v739,v803,v1226,v992,v1227,v1228,v1229,v1230,v1231,v1232,v942,v1233,v983,v1234,v1205,v984,v1135,v1166,v1235])
  (consBan h1252 (consBan h1253 (consBan h1254 (consBan h1255 (consBan h1256 (consBan h1257 (consBan h1258 (consBan h51 (consBan h55 (consBan h1259 (consBan h112 (consBan h1260 (consBan h1261 (consBan h1262 (consBan h1263 (consBan h1264 (consBan h1265 (consBan h214 (consBan h1266 (consBan h245 (consBan h277 (consBan h305 (consBan h392 (consBan h1267 (consBan h1268 (consBan h1269 (consBan h1270 (consBan h1271 (consBan h714 (consBan h1272 (consBan h754 (consBan h820 (consBan h1273 (consBan h1274 (consBan h1275 (consBan h1276 (consBan h1277 (consBan h1278 (consBan h1279 (consBan h1280 (consBan h964 (consBan h1281 (consBan h1007 (consBan h1282 (consBan h1250 (consBan h1008 (consBan h1172 (consBan h1206 (consBan h1283 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v1244 : List ℕ := [w5,w1,w2,w65,w3,w4]

theorem h1295 : Ban 60 5 v1244 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1245 : List ℕ := [w9,w1,w2,w65,w3,w4]

theorem h1296 : Ban 60 5 v1245 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1246 : List ℕ := [w119,w1,w2,w65,w3,w4]

theorem h1297 : Ban 60 5 v1246 := viaSmall (by decide +kernel) (by decide)

def v1247 : List ℕ := [w14,w1,w2,w65,w3,w4]

theorem h1298 : Ban 60 5 v1247 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1248 : List ℕ := [w16,w1,w2,w65,w3,w4]

theorem h1299 : Ban 60 5 v1248 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1249 : List ℕ := [w18,w1,w2,w65,w3,w4]

theorem h1300 : Ban 60 5 v1249 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1250 : List ℕ := [w128,w1,w2,w65,w3,w4]

theorem h1301 : Ban 60 5 v1250 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

theorem h1302 : Ban 60 5 v117 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1251 : List ℕ := [w121,w1,w2,w65,w3,w4]

theorem h1303 : Ban 60 5 v1251 := viaSmall (by decide +kernel) (by decide)

def v1252 : List ℕ := [w28,w1,w2,w65,w3,w4]

theorem h1304 : Ban 60 5 v1252 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1253 : List ℕ := [w85,w1,w2,w65,w3,w4]

theorem h1305 : Ban 60 5 v1253 := viaSmall (by decide +kernel) (by decide)

def v1254 : List ℕ := [w1,w53,w2,w65,w3,w4]

theorem h1306 : Ban 60 5 v1254 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1255 : List ℕ := [w1,w129,w2,w65,w3,w4]

theorem h1307 : Ban 60 5 v1255 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1256 : List ℕ := [w1,w55,w2,w65,w3,w4]

theorem h1308 : Ban 60 5 v1256 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

theorem h1309 : Ban 60 5 v611 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1257 : List ℕ := [w1,w56,w2,w65,w3,w4]

theorem h1310 : Ban 60 5 v1257 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1258 : List ℕ := [w1,w2,w130,w65,w3,w4]

theorem h1311 : Ban 60 5 v1258 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1259 : List ℕ := [w1,w2,w130,w3,w4]

theorem h1312 : Ban 60 5 v1259 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1260 : List ℕ := [w1,w2,w123,w65,w3,w4]

theorem h1313 : Ban 60 5 v1260 := viaSmall (by decide +kernel) (by decide)

def v1261 : List ℕ := [w1,w2,w65,w105,w3,w4]

theorem h1314 : Ban 60 5 v1261 := viaSmall (by decide +kernel) (by decide)

def v1262 : List ℕ := [w1,w2,w65,w35,w3,w4]

theorem h1315 : Ban 60 5 v1262 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1263 : List ℕ := [w1,w2,w65,w36,w3,w4]

theorem h1316 : Ban 60 5 v1263 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1264 : List ℕ := [w1,w2,w65,w131,w3,w4]

theorem h1317 : Ban 60 5 v1264 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1265 : List ℕ := [w1,w2,w65,w38,w3,w4]

theorem h1318 : Ban 60 5 v1265 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1266 : List ℕ := [w1,w2,w65,w39,w3,w4]

theorem h1319 : Ban 60 5 v1266 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1267 : List ℕ := [w1,w2,w65,w3,w132,w4]

theorem h1320 : Ban 60 5 v1267 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1268 : List ℕ := [w1,w2,w65,w3,w59,w4]

theorem h1321 : Ban 60 5 v1268 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1269 : List ℕ := [w1,w2,w65,w3,w60,w4]

theorem h1322 : Ban 60 5 v1269 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1270 : List ℕ := [w1,w2,w65,w3,w133,w4]

theorem h1323 : Ban 60 5 v1270 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1271 : List ℕ := [w1,w2,w65,w3,w43,w4]

theorem h1324 : Ban 60 5 v1271 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1272 : List ℕ := [w1,w2,w65,w3,w4,w122]

theorem h1325 : Ban 60 5 v1272 := viaSmall (by decide +kernel) (by decide)

def v1273 : List ℕ := [w1,w2,w3,w133,w4]

theorem h1326 : Ban 60 5 v1273 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h1294 : Ban 60 6 v165 := viaBranch (ws := [v1244,v1245,v1246,v1247,v1248,v1249,v1250,v139,v117,v163,v1251,v1252,v218,v251,v282,v1253,v336,v1254,v1255,v1256,v611,v1257,v1258,v1259,v1260,v602,v1261,v660,v1262,v1263,v1264,v1265,v1266,v812,v1267,v865,v1268,v1269,v1270,v1271,v906,v1272,v943,v1003,v1062,v1102,v1167,v1273,v604])
  (consBan h1295 (consBan h1296 (consBan h1297 (consBan h1298 (consBan h1299 (consBan h1300 (consBan h1301 (consBan h139 (consBan h1302 (consBan h163 (consBan h1303 (consBan h1304 (consBan h218 (consBan h256 (consBan h287 (consBan h1305 (consBan h341 (consBan h1306 (consBan h1307 (consBan h1308 (consBan h1309 (consBan h1310 (consBan h1311 (consBan h1312 (consBan h1313 (consBan h614 (consBan h1314 (consBan h672 (consBan h1315 (consBan h1316 (consBan h1317 (consBan h1318 (consBan h1319 (consBan h829 (consBan h1320 (consBan h882 (consBan h1321 (consBan h1322 (consBan h1323 (consBan h1324 (consBan h926 (consBan h1325 (consBan h965 (consBan h1027 (consBan h1091 (consBan h1136 (consBan h1207 (consBan h1326 (consBan h616 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v1274 : List ℕ := [w5,w1,w2,w3,w41,w4]

theorem h1328 : Ban 60 5 v1274 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1275 : List ℕ := [w9,w1,w2,w3,w41,w4]

theorem h1329 : Ban 60 5 v1275 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1276 : List ℕ := [w14,w1,w2,w3,w41,w4]

theorem h1330 : Ban 60 5 v1276 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1277 : List ℕ := [w114,w1,w2,w3,w41,w4]

theorem h1331 : Ban 60 5 v1277 := viaSmall (by decide +kernel) (by decide)

def v1278 : List ℕ := [w16,w1,w2,w3,w41,w4]

theorem h1332 : Ban 60 5 v1278 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1279 : List ℕ := [w166,w1,w2,w3,w41,w4]

theorem h1333 : Ban 60 5 v1279 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1280 : List ℕ := [w18,w1,w2,w3,w41,w4]

theorem h1334 : Ban 60 5 v1280 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

theorem h1335 : Ban 60 5 v64 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1281 : List ℕ := [w28,w1,w2,w3,w41,w4]

theorem h1336 : Ban 60 5 v1281 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1282 : List ℕ := [w116,w1,w2,w3,w41,w4]

theorem h1337 : Ban 60 5 v1282 := viaSmall (by decide +kernel) (by decide)

def v1283 : List ℕ := [w80,w1,w2,w3,w41,w4]

theorem h1338 : Ban 60 5 v1283 := viaSmall (by decide +kernel) (by decide)

def v1284 : List ℕ := [w1,w53,w2,w3,w41,w4]

theorem h1339 : Ban 60 5 v1284 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1285 : List ℕ := [w1,w124,w2,w3,w41,w4]

theorem h1340 : Ban 60 5 v1285 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1286 : List ℕ := [w1,w55,w2,w3,w41,w4]

theorem h1341 : Ban 60 5 v1286 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1287 : List ℕ := [w1,w56,w2,w3,w41,w4]

theorem h1342 : Ban 60 5 v1287 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1288 : List ℕ := [w1,w2,w159,w3,w41,w4]

theorem h1343 : Ban 60 5 v1288 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1289 : List ℕ := [w1,w2,w35,w3,w41,w4]

theorem h1344 : Ban 60 5 v1289 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1290 : List ℕ := [w1,w2,w36,w3,w41,w4]

theorem h1345 : Ban 60 5 v1290 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1291 : List ℕ := [w1,w2,w167,w3,w41,w4]

theorem h1346 : Ban 60 5 v1291 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1292 : List ℕ := [w1,w2,w38,w3,w41,w4]

theorem h1347 : Ban 60 5 v1292 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

theorem h1348 : Ban 60 5 v821 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1293 : List ℕ := [w1,w2,w39,w3,w41,w4]

theorem h1349 : Ban 60 5 v1293 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1294 : List ℕ := [w1,w2,w3,w168,w41,w4]

theorem h1350 : Ban 60 5 v1294 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1295 : List ℕ := [w1,w2,w3,w168,w4]

theorem h1351 : Ban 60 5 v1295 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1296 : List ℕ := [w1,w2,w3,w118,w41,w4]

theorem h1352 : Ban 60 5 v1296 := viaSmall (by decide +kernel) (by decide)

def v1297 : List ℕ := [w1,w2,w3,w41,w107,w4]

theorem h1353 : Ban 60 5 v1297 := viaSmall (by decide +kernel) (by decide)

def v1298 : List ℕ := [w1,w2,w3,w41,w59,w4]

theorem h1354 : Ban 60 5 v1298 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1299 : List ℕ := [w1,w2,w3,w41,w60,w4]

theorem h1355 : Ban 60 5 v1299 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1300 : List ℕ := [w1,w2,w3,w41,w133,w4]

theorem h1356 : Ban 60 5 v1300 := cutTest_ok p98 (extra := []) minorant98 (by decide) (by decide +kernel)

def v1301 : List ℕ := [w1,w2,w3,w41,w43,w4]

theorem h1357 : Ban 60 5 v1301 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v1302 : List ℕ := [w1,w2,w3,w41,w4,w117]

theorem h1358 : Ban 60 5 v1302 := viaSmall (by decide +kernel) (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h1327 : Ban 60 6 v114 := viaBranch (ws := [v1274,v1275,v1276,v1277,v1278,v1279,v1280,v60,v96,v64,v109,v1281,v1282,v252,v1283,v283,v337,v1284,v1285,v1286,v1287,v603,v1288,v661,v1289,v1290,v1291,v1292,v821,v1293,v1294,v1295,v1296,v813,v1297,v866,v1298,v1299,v1300,v1301,v907,v944,v1302,v1006,v1063,v1103,v1273,v814,v1235])
  (consBan h1328 (consBan h1329 (consBan h1330 (consBan h1331 (consBan h1332 (consBan h1333 (consBan h1334 (consBan h60 (consBan h96 (consBan h1335 (consBan h109 (consBan h1336 (consBan h1337 (consBan h257 (consBan h1338 (consBan h288 (consBan h342 (consBan h1339 (consBan h1340 (consBan h1341 (consBan h1342 (consBan h615 (consBan h1343 (consBan h673 (consBan h1344 (consBan h1345 (consBan h1346 (consBan h1347 (consBan h1348 (consBan h1349 (consBan h1350 (consBan h1351 (consBan h1352 (consBan h830 (consBan h1353 (consBan h883 (consBan h1354 (consBan h1355 (consBan h1356 (consBan h1357 (consBan h927 (consBan h966 (consBan h1358 (consBan h1030 (consBan h1092 (consBan h1137 (consBan h1326 (consBan h831 (consBan h1283 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h0 : Ban 60 7 v0 := viaBranch (ws := [v1,v3,v4,v6,v7,v8,v9,v10,v11,v63,v64,v115,v116,v117,v167,v168,v169,v170,v219,v253,v284,v312,v304,v438,v439,v440,v246,v484,v485,v333,v621,v662,v663,v664,v665,v248,v704,v705,v279,v831,v867,v868,v280,v869,v870,v908,v909,v250,v861,v657,v699,v216,v480,v62,v165,v114])
  (consBan h1 (consBan h3 (consBan h4 (consBan h6 (consBan h7 (consBan h8 (consBan h9 (consBan h10 (consBan h11 (consBan h63 (consBan h64 (consBan h115 (consBan h116 (consBan h117 (consBan h167 (consBan h168 (consBan h169 (consBan h170 (consBan h219 (consBan h258 (consBan h289 (consBan h317 (consBan h343 (consBan h445 (consBan h446 (consBan h447 (consBan h491 (consBan h492 (consBan h493 (consBan h540 (consBan h633 (consBan h674 (consBan h675 (consBan h676 (consBan h677 (consBan h716 (consBan h717 (consBan h718 (consBan h759 (consBan h848 (consBan h884 (consBan h885 (consBan h886 (consBan h887 (consBan h888 (consBan h928 (consBan h929 (consBan h967 (consBan h1047 (consBan h1093 (consBan h1138 (consBan h1173 (consBan h1218 (consBan h1251 (consBan h1294 (consBan h1327 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

theorem borneCinq : Wide 60 7 cinqBase := by
  apply widen (by decide +kernel)
  intro n hn hl
  exact h0 n hn (by simpa only [show cinqBase.toFinset = v0.toFinset by decide +kernel] using hl)
end Travail11645


namespace Travail11645
open M10720 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def bouts : List ℕ := [0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6]

def graph (x : Fin 7 → Bool) := decide (∃ i < bouts.length / 2,
  (List.ofFn x).getD (bouts.getD (2*i) 0) false = true ∧
  (List.ofFn x).getD (bouts.getD (2*i+1) 0) false = true)

def temoin : List Gate := [
  ⟨.or,[0,3]⟩, ⟨.and,[7,5]⟩, ⟨.and,[0,3]⟩, ⟨.or,[8,9]⟩,
  ⟨.or,[1,6]⟩, ⟨.or,[4,5]⟩, ⟨.and,[11,12]⟩,
  ⟨.or,[1,2]⟩, ⟨.and,[6,14]⟩, ⟨.or,[13,15]⟩, ⟨.or,[10,16]⟩]

theorem legalite : ∀ g ∈ temoin, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [temoin]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
theorem correct : ∀ x : Fin 7 → Bool, Circuit.eval ⟨temoin,17⟩ (List.ofFn x) = graph x := by
  decide +kernel

def restriction : Projection 62 60 := pick (List.range 60) (by simp)
  (by intro i hi; have := List.mem_range.mp hi; omega) (by decide)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
theorem couper (h : Wide 60 7 cinqBase) : Ban 62 9 septBase := by
  apply viaCut restriction h <;> decide +kernel

def sample (bank : ℕ) (i : Fin 62) (j : Fin 7) := bank.testBit (7*i.val+j.val)
def seeds : List Wire := septBase.map (fun a => (false,a))
set_option maxHeartbeats 1000000 in
theorem listed : ∀ i : Fin 62, seeds.map (read i.val)=List.ofFn (sample posBits i) ∧
    seeds.map (read (62+i.val))=List.ofFn (sample negBits i) := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem labels : ∀ i : Fin 62, graph (sample posBits i)=true ∧ graph (sample negBits i)=false := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem essential : ∀ a∈septBase, ∃ i : Fin 62, ∀ b∈septBase, b.testBit i.val≠b.testBit (62+i.val) → b=a := by decide +kernel
theorem initial {k S} (live : Live 62 k S) (sub : ∀ a∈S,a∈septBase) : S=septBase.toFinset := by
  apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
  intro a ha
  obtain ⟨i,h⟩ := essential a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
  exact h b (sub b hb) sep ▸ hb
theorem trace (C : Circuit) (fan : FanInTwo C) (eq : circuitFun 7 C=graph) :
    ∃ k≤C.gates.countP counted, Live 62 k septBase.toFinset := by
  let final := execute C.gates seeds
  let out := final.getD C.output zero
  have ev (i : ℕ) : read i out = C.eval (seeds.map (read i)) := by
    rw [show read i out = (final.map (read i)).getD C.output false from (read_get i final C.output).symm]
    rw [show final=execute C.gates seeds from rfl,execute_read i _ _ fan];rfl
  have result (x : Fin 7 → Bool) : C.eval (List.ofFn x)=graph x := congrFun eq x
  have good : Good 62 out.2 := by
    intro i hi same
    let j : Fin 62 := ⟨i,hi⟩
    have diff : M10720.read i out=M10720.read (62+i) out := by simp only [M10720.read,same]
    have p := ev i;have n := ev (62+i)
    rw [(listed j).1,result,(labels j).1] at p
    rw [(listed j).2,result,(labels j).2] at n
    rw [p,n] at diff;contradiction
  have nz : out.2≠0 := by
    intro z;have bad := good 0 (by decide);simp [z] at bad
  have found : out.2∈ reps final := (get_simple final C.output).resolve_left nz
  obtain ⟨k,S,limit,live,sub⟩ := extract good nz C.gates seeds found
  have stays : ∀ a∈S, a∈septBase := by simpa [reps,seeds,List.map_map,Function.comp_def] using sub
  exact ⟨k,limit,initial live stays ▸ live⟩


theorem lt_count {gs : List Gate} (h : ∃ g ∈ gs, g.op = .not) : gs.countP counted < gs.length := by
  apply Nat.lt_of_le_of_ne List.countP_le_length
  intro eq
  obtain ⟨g,hg,hop⟩ := h
  have bad := List.countP_eq_length.mp eq g hg
  simp [counted,hop] at bad


theorem finir (h : M10720.Wide 60 7 cinqBase) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  have cert := couper h
  intro gs o hfan _ he
  by_cases hn : ∃ g ∈ gs, g.op = .not
  · have fan : FanInTwo ⟨gs,o⟩ := fun g hg => ⟨(hfan g hg).1,(hfan g hg).2⟩
    obtain ⟨k,kle,live⟩ := trace ⟨gs,o⟩ fan (funext he)
    have grand : 10 ≤ k := by
      by_contra! small
      exact cert k (by omega) live
    have less := lt_count hn
    change k ≤ gs.countP counted at kle
    exact ⟨temoin,17,legalite,by change 11 ≤ gs.length; omega,correct⟩
  · refine ⟨gs,o,?_,le_rfl,he⟩
    intro g hg
    exact ⟨(hfan g hg).1.imp_right (fun h => h.resolve_right (fun e => hn ⟨g,hg,e⟩)),(hfan g hg).2⟩


end Travail11645


end PEqualNP.Outside.L_meta_11645

theorem PEqualNP.Outside.L_meta_11645 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  exact PEqualNP.Outside.L_meta_11645.Travail11645.finir PEqualNP.Outside.L_meta_11645.Travail11645.borneCinq
