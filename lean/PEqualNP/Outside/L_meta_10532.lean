import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10532

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

def fil0 : ℕ := 0x842108400f83ff
def fil1 : ℕ := 0x108421081f07c1f
def fil2 : ℕ := 0x21084213e007fe0
def fil3 : ℕ := 0x42108423fff8000
def etat0 : List ℕ := [fil0,fil1,fil2,fil3]
def fil4 : ℕ := 0x1f
def etat1 : List ℕ := [fil4,fil0,fil1,fil2,fil3]
def fil5 : ℕ := 0x842108400f83e0
def etat2 : List ℕ := [fil4,fil5,fil1,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve4 : Ban 30 4 etat2 := viaSmall (by decide +kernel) (by decide)
def fil6 : ℕ := 0x108421081f07c00
def etat3 : List ℕ := [fil4,fil0,fil6,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve5 : Ban 30 4 etat3 := viaSmall (by decide +kernel) (by decide)
def fil7 : ℕ := 0x42108423fff801f
def etat4 : List ℕ := [fil4,fil0,fil1,fil2,fil7]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve6 : Ban 30 4 etat4 := viaSmall (by decide +kernel) (by decide)
def fil8 : ℕ := 0x21084213e007fff
def etat5 : List ℕ := [fil4,fil0,fil1,fil8,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve7 : Ban 30 4 etat5 := viaSmall (by decide +kernel) (by decide)
def fil9 : ℕ := 0x18c6318c1ffffff
def etat6 : List ℕ := [fil4,fil0,fil9,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve8 : Ban 30 4 etat6 := viaSmall (by decide +kernel) (by decide)
def etat7 : List ℕ := [fil4,fil1,fil9,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve9 : Ban 30 4 etat7 := viaSmall (by decide +kernel) (by decide)
def etat8 : List ℕ := [fil4,fil9,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve10 : Ban 30 4 etat8 := viaSmall (by decide +kernel) (by decide)
def etat9 : List ℕ := [fil5,fil0,fil1,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve11 : Ban 30 4 etat9 := viaSmall (by decide +kernel) (by decide)
def etat10 : List ℕ := [fil0,fil6,fil1,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve12 : Ban 30 4 etat10 := viaSmall (by decide +kernel) (by decide)
def etat11 : List ℕ := [fil0,fil1,fil2,fil8,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve13 : Ban 30 4 etat11 := viaSmall (by decide +kernel) (by decide)
def etat12 : List ℕ := [fil0,fil1,fil2,fil3,fil7]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve14 : Ban 30 4 etat12 := viaSmall (by decide +kernel) (by decide)
def etat13 : List ℕ := [fil0,fil1,fil2,fil7]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve15 : Ban 30 4 etat13 := viaSmall (by decide +kernel) (by decide)
def etat14 : List ℕ := [fil0,fil1,fil8,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve16 : Ban 30 4 etat14 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve3 : Ban 30 5 etat1 := viaBranch (ws := [etat2,etat3,etat4,etat5,etat6,etat7,etat8,etat9,etat10,etat11,etat12,etat13,etat14])
  (consBan preuve4 (consBan preuve5 (consBan preuve6 (consBan preuve7 (consBan preuve8 (consBan preuve9 (consBan preuve10 (consBan preuve11 (consBan preuve12 (consBan preuve13 (consBan preuve14 (consBan preuve15 (consBan preuve16 (nilBan _ _))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def fil10 : ℕ := 0x3e0
def etat15 : List ℕ := [fil10,fil0,fil1,fil2,fil3]
def proj0 : Projection 30 30 := pick [5,7,6,8,9,0,2,1,3,4,10,12,11,13,14,15,17,16,18,19,25,27,26,28,29,20,22,21,23,24] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve17 : Ban 30 5 etat15 := viaPerm proj0 proj0 preuve3 (by decide +kernel) (by decide +kernel)
def fil11 : ℕ := 0x7c00
def etat16 : List ℕ := [fil11,fil0,fil1,fil2,fil3]
def proj1 : Projection 30 30 := pick [11,12,10,13,14,1,2,0,3,4,6,7,5,8,9,21,22,20,23,24,26,27,25,28,29,16,17,15,18,19] rfl (by decide +kernel) (by decide)
def proj2 : Projection 30 30 := pick [7,5,6,8,9,12,10,11,13,14,2,0,1,3,4,27,25,26,28,29,17,15,16,18,19,22,20,21,23,24] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve18 : Ban 30 5 etat16 := viaPerm proj1 proj2 preuve3 (by decide +kernel) (by decide +kernel)
def fil12 : ℕ := 0xf8000
def etat17 : List ℕ := [fil12,fil0,fil1,fil2,fil3]
def proj3 : Projection 30 30 := pick [15,18,16,17,19,0,3,1,2,4,20,23,21,22,24,5,8,6,7,9,25,28,26,27,29,10,13,11,12,14] rfl (by decide +kernel) (by decide)
def proj4 : Projection 30 30 := pick [5,7,8,6,9,15,17,18,16,19,25,27,28,26,29,0,2,3,1,4,10,12,13,11,14,20,22,23,21,24] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve19 : Ban 30 5 etat17 := viaPerm proj3 proj4 preuve3 (by decide +kernel) (by decide +kernel)
def fil13 : ℕ := 0x1f00000
def etat18 : List ℕ := [fil13,fil0,fil1,fil2,fil3]
def proj5 : Projection 30 30 := pick [21,23,20,22,24,1,3,0,2,4,16,18,15,17,19,11,13,10,12,14,26,28,25,27,29,6,8,5,7,9] rfl (by decide +kernel) (by decide)
def proj6 : Projection 30 30 := pick [7,5,8,6,9,27,25,28,26,29,17,15,18,16,19,12,10,13,11,14,2,0,3,1,4,22,20,23,21,24] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve20 : Ban 30 5 etat18 := viaPerm proj5 proj6 preuve3 (by decide +kernel) (by decide +kernel)
def fil14 : ℕ := 0x3e000000
def etat19 : List ℕ := [fil14,fil0,fil1,fil2,fil3]
def proj7 : Projection 30 30 := pick [27,28,25,26,29,7,8,5,6,9,17,18,15,16,19,12,13,10,11,14,22,23,20,21,24,2,3,0,1,4] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve21 : Ban 30 5 etat19 := viaPerm proj7 proj7 preuve3 (by decide +kernel) (by decide +kernel)
def fil15 : ℕ := 0x842108400003ff
def etat20 : List ℕ := [fil15,fil0,fil1,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve23 : Ban 30 4 etat1 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve24 : Ban 30 4 etat15 := viaSmall (by decide +kernel) (by decide)
def etat21 : List ℕ := [fil12,fil15,fil1,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve25 : Ban 30 4 etat21 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve26 : Ban 30 4 etat17 := viaSmall (by decide +kernel) (by decide)
def fil16 : ℕ := 0x8421084000001f
def etat22 : List ℕ := [fil16,fil0,fil1,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve27 : Ban 30 4 etat22 := viaSmall (by decide +kernel) (by decide)
def fil17 : ℕ := 0x842108400003e0
def etat23 : List ℕ := [fil17,fil0,fil1,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve28 : Ban 30 4 etat23 := viaSmall (by decide +kernel) (by decide)
def fil18 : ℕ := 0x842108400f801f
def etat24 : List ℕ := [fil15,fil18,fil1,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve29 : Ban 30 4 etat24 := viaSmall (by decide +kernel) (by decide)
def etat25 : List ℕ := [fil15,fil5,fil1,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve30 : Ban 30 4 etat25 := viaSmall (by decide +kernel) (by decide)
def fil19 : ℕ := 0x42108423ff00000
def etat26 : List ℕ := [fil15,fil0,fil1,fil2,fil19]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve31 : Ban 30 4 etat26 := viaSmall (by decide +kernel) (by decide)
def fil20 : ℕ := 0x4a5294a7fff83ff
def etat27 : List ℕ := [fil15,fil0,fil1,fil2,fil20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve32 : Ban 30 4 etat27 := viaSmall (by decide +kernel) (by decide)
def etat28 : List ℕ := [fil15,fil1,fil9,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve33 : Ban 30 4 etat28 := viaSmall (by decide +kernel) (by decide)
def fil21 : ℕ := 0x294a5297e0fffff
def etat29 : List ℕ := [fil15,fil1,fil2,fil21,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve34 : Ban 30 4 etat29 := viaSmall (by decide +kernel) (by decide)
def etat30 : List ℕ := [fil15,fil1,fil2,fil19,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve35 : Ban 30 4 etat30 := viaSmall (by decide +kernel) (by decide)
def fil22 : ℕ := 0x18c6318c1f07fff
def etat31 : List ℕ := [fil0,fil1,fil22,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve36 : Ban 30 4 etat31 := viaSmall (by decide +kernel) (by decide)
def fil23 : ℕ := 0x21084213e007c00
def etat32 : List ℕ := [fil0,fil1,fil23,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve37 : Ban 30 4 etat32 := viaSmall (by decide +kernel) (by decide)
def fil24 : ℕ := 0x294a5297e007fff
def etat33 : List ℕ := [fil0,fil1,fil2,fil24,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve38 : Ban 30 4 etat33 := viaSmall (by decide +kernel) (by decide)
def etat34 : List ℕ := [fil0,fil1,fil2,fil3,fil20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve39 : Ban 30 4 etat34 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve22 : Ban 30 5 etat20 := viaBranch (ws := [etat1,etat15,etat21,etat17,etat22,etat23,etat24,etat25,etat26,etat27,etat28,etat29,etat30,etat10,etat31,etat32,etat33,etat34])
  (consBan preuve23 (consBan preuve24 (consBan preuve25 (consBan preuve26 (consBan preuve27 (consBan preuve28 (consBan preuve29 (consBan preuve30 (consBan preuve31 (consBan preuve32 (consBan preuve33 (consBan preuve34 (consBan preuve35 (consBan preuve12 (consBan preuve36 (consBan preuve37 (consBan preuve38 (consBan preuve39 (nilBan _ _)))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def etat35 : List ℕ := [fil18,fil0,fil1,fil2,fil3]
def proj8 : Projection 30 30 := pick [0,1,3,2,4,15,16,18,17,19,20,21,23,22,24,5,6,8,7,9,10,11,13,12,14,25,26,28,27,29] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve40 : Ban 30 5 etat35 := viaPerm proj8 proj8 preuve22 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve41 : Ban 30 5 etat9 := viaPerm proj4 proj3 preuve22 (by decide +kernel) (by decide +kernel)
def fil25 : ℕ := 0x108421080007c1f
def etat36 : List ℕ := [fil0,fil25,fil1,fil2,fil3]
def proj9 : Projection 30 30 := pick [1,0,2,3,4,11,10,12,13,14,6,5,7,8,9,21,20,22,23,24,16,15,17,18,19,26,25,27,28,29] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve42 : Ban 30 5 etat36 := viaPerm proj9 proj9 preuve22 (by decide +kernel) (by decide +kernel)
def fil26 : ℕ := 0x108421081f0001f
def etat37 : List ℕ := [fil0,fil26,fil1,fil2,fil3]
def proj10 : Projection 30 30 := pick [1,0,3,2,4,21,20,23,22,24,16,15,18,17,19,11,10,13,12,14,6,5,8,7,9,26,25,28,27,29] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve43 : Ban 30 5 etat37 := viaPerm proj10 proj10 preuve22 (by decide +kernel) (by decide +kernel)
def proj11 : Projection 30 30 := pick [11,12,13,10,14,21,22,23,20,24,26,27,28,25,29,1,2,3,0,4,6,7,8,5,9,16,17,18,15,19] rfl (by decide +kernel) (by decide)
def proj12 : Projection 30 30 := pick [18,15,16,17,19,23,20,21,22,24,3,0,1,2,4,28,25,26,27,29,8,5,6,7,9,13,10,11,12,14] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve44 : Ban 30 5 etat10 := viaPerm proj11 proj12 preuve22 (by decide +kernel) (by decide +kernel)
def etat38 : List ℕ := [fil0,fil1,fil9,fil2,fil3]
def fil27 : ℕ := 0x7fe0
def etat39 : List ℕ := [fil27,fil0,fil1,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve46 : Ban 30 4 etat39 := viaSmall (by decide +kernel) (by decide)
def fil28 : ℕ := 0x1ff8000
def etat40 : List ℕ := [fil28,fil0,fil1,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve47 : Ban 30 4 etat40 := viaSmall (by decide +kernel) (by decide)
def etat41 : List ℕ := [fil18,fil1,fil9,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve48 : Ban 30 4 etat41 := viaSmall (by decide +kernel) (by decide)
def etat42 : List ℕ := [fil5,fil0,fil9,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve49 : Ban 30 4 etat42 := viaSmall (by decide +kernel) (by decide)
def etat43 : List ℕ := [fil0,fil25,fil9,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve50 : Ban 30 4 etat43 := viaSmall (by decide +kernel) (by decide)
def etat44 : List ℕ := [fil0,fil26,fil9,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve51 : Ban 30 4 etat44 := viaSmall (by decide +kernel) (by decide)
def fil29 : ℕ := 0x18c6318c0007fff
def etat45 : List ℕ := [fil0,fil1,fil29,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve52 : Ban 30 4 etat45 := viaSmall (by decide +kernel) (by decide)
def fil30 : ℕ := 0x18c6318c1ff801f
def etat46 : List ℕ := [fil0,fil1,fil30,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve53 : Ban 30 4 etat46 := viaSmall (by decide +kernel) (by decide)
def fil31 : ℕ := 0x21084213e000000
def etat47 : List ℕ := [fil0,fil1,fil31,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve54 : Ban 30 4 etat47 := viaSmall (by decide +kernel) (by decide)
def fil32 : ℕ := 0x39ce739ffffffff
def etat48 : List ℕ := [fil0,fil1,fil2,fil32,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve55 : Ban 30 4 etat48 := viaSmall (by decide +kernel) (by decide)
def fil33 : ℕ := 0x42108423e000000
def etat49 : List ℕ := [fil0,fil1,fil2,fil33,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve56 : Ban 30 4 etat49 := viaSmall (by decide +kernel) (by decide)
def fil34 : ℕ := 0x5ad6b5affffffff
def etat50 : List ℕ := [fil0,fil1,fil2,fil3,fil34]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve57 : Ban 30 4 etat50 := viaSmall (by decide +kernel) (by decide)
def fil35 : ℕ := 0x318c631bff07fff
def etat51 : List ℕ := [fil0,fil9,fil2,fil35,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve58 : Ban 30 4 etat51 := viaSmall (by decide +kernel) (by decide)
def fil36 : ℕ := 0x5294a52bffffc1f
def etat52 : List ℕ := [fil0,fil9,fil2,fil3,fil36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve59 : Ban 30 4 etat52 := viaSmall (by decide +kernel) (by decide)
def etat53 : List ℕ := [fil6,fil1,fil9,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve60 : Ban 30 4 etat53 := viaSmall (by decide +kernel) (by decide)
def etat54 : List ℕ := [fil1,fil9,fil2,fil21,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve61 : Ban 30 4 etat54 := viaSmall (by decide +kernel) (by decide)
def etat55 : List ℕ := [fil1,fil9,fil2,fil3,fil20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve62 : Ban 30 4 etat55 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve45 : Ban 30 5 etat38 := viaBranch (ws := [etat6,etat7,etat8,etat39,etat40,etat28,etat41,etat9,etat42,etat43,etat44,etat10,etat45,etat46,etat47,etat48,etat49,etat50,etat51,etat52,etat53,etat54,etat55])
  (consBan preuve8 (consBan preuve9 (consBan preuve10 (consBan preuve46 (consBan preuve47 (consBan preuve33 (consBan preuve48 (consBan preuve11 (consBan preuve49 (consBan preuve50 (consBan preuve51 (consBan preuve12 (consBan preuve52 (consBan preuve53 (consBan preuve54 (consBan preuve55 (consBan preuve56 (consBan preuve57 (consBan preuve58 (consBan preuve59 (consBan preuve60 (consBan preuve61 (consBan preuve62 (nilBan _ _))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def fil37 : ℕ := 0x210842100007fe0
def etat56 : List ℕ := [fil0,fil1,fil37,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve63 : Ban 30 5 etat56 := viaPerm proj2 proj1 preuve22 (by decide +kernel) (by decide +kernel)
def fil38 : ℕ := 0x21084213e0003e0
def etat57 : List ℕ := [fil0,fil1,fil38,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve64 : Ban 30 5 etat57 := viaPerm proj6 proj5 preuve22 (by decide +kernel) (by decide +kernel)
def proj13 : Projection 30 30 := pick [12,11,13,10,14,27,26,28,25,29,22,21,23,20,24,7,6,8,5,9,2,1,3,0,4,17,16,18,15,19] rfl (by decide +kernel) (by decide)
def proj14 : Projection 30 30 := pick [23,21,20,22,24,18,16,15,17,19,3,1,0,2,4,28,26,25,27,29,13,11,10,12,14,8,6,5,7,9] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve65 : Ban 30 5 etat32 := viaPerm proj13 proj14 preuve22 (by decide +kernel) (by decide +kernel)
def etat58 : List ℕ := [fil0,fil1,fil2,fil21,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve66 : Ban 30 5 etat58 := viaPerm proj0 proj0 preuve45 (by decide +kernel) (by decide +kernel)
def etat59 : List ℕ := [fil0,fil1,fil2,fil35,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve67 : Ban 30 5 etat59 := viaPerm proj1 proj2 preuve45 (by decide +kernel) (by decide +kernel)
def fil39 : ℕ := 0x421084201ff8000
def etat60 : List ℕ := [fil0,fil1,fil2,fil39,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve68 : Ban 30 5 etat60 := viaPerm proj12 proj11 preuve22 (by decide +kernel) (by decide +kernel)
def fil40 : ℕ := 0x42108423e0f8000
def etat61 : List ℕ := [fil0,fil1,fil2,fil40,fil3]
def proj15 : Projection 30 30 := pick [18,15,17,16,19,28,25,27,26,29,8,5,7,6,9,23,20,22,21,24,3,0,2,1,4,13,10,12,11,14] rfl (by decide +kernel) (by decide)
def proj16 : Projection 30 30 := pick [21,23,22,20,24,11,13,12,10,14,26,28,27,25,29,1,3,2,0,4,16,18,17,15,19,6,8,7,5,9] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve69 : Ban 30 5 etat61 := viaPerm proj15 proj16 preuve22 (by decide +kernel) (by decide +kernel)
def etat62 : List ℕ := [fil0,fil1,fil2,fil19,fil3]
def proj17 : Projection 30 30 := pick [23,21,22,20,24,28,26,27,25,29,13,11,12,10,14,18,16,17,15,19,3,1,2,0,4,8,6,7,5,9] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve70 : Ban 30 5 etat62 := viaPerm proj17 proj17 preuve22 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve71 : Ban 30 5 etat34 := viaPerm proj3 proj4 preuve45 (by decide +kernel) (by decide +kernel)
def etat63 : List ℕ := [fil0,fil1,fil2,fil3,fil36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve72 : Ban 30 5 etat63 := viaPerm proj5 proj6 preuve45 (by decide +kernel) (by decide +kernel)
def fil41 : ℕ := 0x6318c633fffffe0
def etat64 : List ℕ := [fil0,fil1,fil2,fil3,fil41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve73 : Ban 30 5 etat64 := viaPerm proj7 proj7 preuve45 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve2 : Ban 30 6 etat0 := viaBranch (ws := [etat1,etat15,etat16,etat17,etat18,etat19,etat20,etat35,etat9,etat36,etat37,etat10,etat38,etat56,etat57,etat32,etat58,etat59,etat60,etat61,etat62,etat34,etat63,etat64])
  (consBan preuve3 (consBan preuve17 (consBan preuve18 (consBan preuve19 (consBan preuve20 (consBan preuve21 (consBan preuve22 (consBan preuve40 (consBan preuve41 (consBan preuve42 (consBan preuve43 (consBan preuve44 (consBan preuve45 (consBan preuve63 (consBan preuve64 (consBan preuve65 (consBan preuve66 (consBan preuve67 (consBan preuve68 (consBan preuve69 (consBan preuve70 (consBan preuve71 (consBan preuve72 (consBan preuve73 (nilBan _ _)))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit0 : Wide 30 6 etat0 := viaSub (ws := [etat0])
  (consBan preuve2 (nilBan _ _))
  (by decide) (by decide +kernel)
def fil42 : ℕ := 0x3f
def fil43 : ℕ := 0x4104104104104100003f000fc0fff
def fil44 : ℕ := 0x82082082082082000fc003f03f03f
def fil45 : ℕ := 0x10410410410410403f000fc003ffc0
def fil46 : ℕ := 0x208208208208208fc0000ffffc0000
def fil47 : ℕ := 0x410410410410410ffffff000000000
def etat65 : List ℕ := [fil42,fil43,fil44,fil45,fil46,fil47]
def proj18 : Projection 60 30 := pick [13,14,15,16,17,25,26,27,28,29,31,32,33,34,35,43,44,45,46,47,49,50,51,52,53,55,56,57,58,59] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve74 : Ban 60 8 etat65 := viaCut proj18 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def fil48 : ℕ := 0xfc0
def etat66 : List ℕ := [fil48,fil43,fil44,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve75 : Ban 60 8 etat66 := viaCut proj18 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def fil49 : ℕ := 0x3f000
def etat67 : List ℕ := [fil49,fil43,fil44,fil45,fil46,fil47]
def proj19 : Projection 60 30 := pick [6,8,9,10,11,18,20,21,22,23,30,32,33,34,35,36,38,39,40,41,48,50,51,52,53,54,56,57,58,59] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve76 : Ban 60 8 etat67 := viaCut proj19 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def fil50 : ℕ := 0xfc0000
def etat68 : List ℕ := [fil50,fil43,fil44,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve77 : Ban 60 8 etat68 := viaCut proj18 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def fil51 : ℕ := 0x3f000000
def etat69 : List ℕ := [fil51,fil43,fil44,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve78 : Ban 60 8 etat69 := viaCut proj19 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def fil52 : ℕ := 0xfc0000000
def etat70 : List ℕ := [fil52,fil43,fil44,fil45,fil46,fil47]
def proj20 : Projection 60 30 := pick [0,1,3,4,5,18,19,21,22,23,24,25,27,28,29,36,37,39,40,41,42,43,45,46,47,54,55,57,58,59] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve79 : Ban 60 8 etat70 := viaCut proj20 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def fil53 : ℕ := 0x3f000000000
def etat71 : List ℕ := [fil53,fil43,fil44,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve80 : Ban 60 8 etat71 := viaCut proj18 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def fil54 : ℕ := 0xfc0000000000
def etat72 : List ℕ := [fil54,fil43,fil44,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve81 : Ban 60 8 etat72 := viaCut proj19 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def fil55 : ℕ := 0x3f000000000000
def etat73 : List ℕ := [fil55,fil43,fil44,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve82 : Ban 60 8 etat73 := viaCut proj20 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def fil56 : ℕ := 0xfc0000000000000
def etat74 : List ℕ := [fil56,fil43,fil44,fil45,fil46,fil47]
def proj21 : Projection 60 30 := pick [0,1,2,4,5,6,7,8,10,11,12,13,14,16,17,36,37,38,40,41,42,43,44,46,47,48,49,50,52,53] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve83 : Ban 60 8 etat74 := viaCut proj21 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def fil57 : ℕ := 0x41041041041041000000000fc0fff
def etat75 : List ℕ := [fil57,fil43,fil44,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve84 : Ban 60 8 etat75 := viaCut proj18 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def fil58 : ℕ := 0x4104104104104100003f000000fff
def etat76 : List ℕ := [fil58,fil43,fil44,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve85 : Ban 60 8 etat76 := viaCut proj18 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def fil59 : ℕ := 0x4104104104104100003f000fc003f
def etat77 : List ℕ := [fil59,fil43,fil44,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve86 : Ban 60 8 etat77 := viaCut proj18 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def fil60 : ℕ := 0x4104104104104100003f000fc0fc0
def etat78 : List ℕ := [fil60,fil43,fil44,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve87 : Ban 60 8 etat78 := viaCut proj18 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def fil61 : ℕ := 0x8208208208208200000003f03f03f
def etat79 : List ℕ := [fil43,fil61,fil44,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve88 : Ban 60 8 etat79 := viaCut proj19 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def fil62 : ℕ := 0x82082082082082000fc000003f03f
def etat80 : List ℕ := [fil43,fil62,fil44,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve89 : Ban 60 8 etat80 := viaCut proj19 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def fil63 : ℕ := 0x82082082082082000fc003f00003f
def etat81 : List ℕ := [fil43,fil63,fil44,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve90 : Ban 60 8 etat81 := viaCut proj19 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def fil64 : ℕ := 0x82082082082082000fc003f03f000
def etat82 : List ℕ := [fil43,fil64,fil44,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve91 : Ban 60 8 etat82 := viaCut proj19 petit0 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve94 : Ban 30 4 etat16 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve95 : Ban 30 4 etat18 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve96 : Ban 30 4 etat19 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve97 : Ban 30 4 etat20 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve98 : Ban 30 4 etat35 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve99 : Ban 30 4 etat36 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve100 : Ban 30 4 etat37 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve101 : Ban 30 4 etat38 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve102 : Ban 30 4 etat56 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve103 : Ban 30 4 etat57 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve104 : Ban 30 4 etat58 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve105 : Ban 30 4 etat59 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve106 : Ban 30 4 etat60 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve107 : Ban 30 4 etat61 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve108 : Ban 30 4 etat62 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve109 : Ban 30 4 etat63 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve110 : Ban 30 4 etat64 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve93 : Ban 30 5 etat0 := viaBranch (ws := [etat1,etat15,etat16,etat17,etat18,etat19,etat20,etat35,etat9,etat36,etat37,etat10,etat38,etat56,etat57,etat32,etat58,etat59,etat60,etat61,etat62,etat34,etat63,etat64])
  (consBan preuve23 (consBan preuve24 (consBan preuve94 (consBan preuve26 (consBan preuve95 (consBan preuve96 (consBan preuve97 (consBan preuve98 (consBan preuve11 (consBan preuve99 (consBan preuve100 (consBan preuve12 (consBan preuve101 (consBan preuve102 (consBan preuve103 (consBan preuve37 (consBan preuve104 (consBan preuve105 (consBan preuve106 (consBan preuve107 (consBan preuve108 (consBan preuve39 (consBan preuve109 (consBan preuve110 (nilBan _ _)))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit1 : Wide 30 5 etat0 := viaSub (ws := [etat0])
  (consBan preuve93 (nilBan _ _))
  (by decide) (by decide +kernel)
def fil65 : ℕ := 0xc30c30c30c30c3000fff03fffffff
def etat83 : List ℕ := [fil42,fil43,fil44,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve111 : Ban 60 7 etat83 := viaCut proj18 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat84 : List ℕ := [fil42,fil43,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve112 : Ban 60 7 etat84 := viaCut proj18 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat85 : List ℕ := [fil42,fil44,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve113 : Ban 60 7 etat85 := viaCut proj19 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat86 : List ℕ := [fil42,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve114 : Ban 60 7 etat86 := viaCut proj18 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def etat87 : List ℕ := [fil48,fil43,fil44,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve115 : Ban 60 7 etat87 := viaCut proj18 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat88 : List ℕ := [fil49,fil43,fil44,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve116 : Ban 60 7 etat88 := viaCut proj19 petit1 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit2 : Wide 30 5 etat38 := viaSub (ws := [etat0,etat38])
  (consBan preuve93 (consBan preuve45 (nilBan _ _)))
  (by decide) (by decide +kernel)
def fil66 : ℕ := 0x3ffc0
def etat89 : List ℕ := [fil66,fil43,fil44,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve117 : Ban 60 7 etat89 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat90 : List ℕ := [fil66,fil43,fil44,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve118 : Ban 60 7 etat90 := viaCut proj20 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat91 : List ℕ := [fil50,fil43,fil44,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve119 : Ban 60 7 etat91 := viaCut proj18 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat92 : List ℕ := [fil51,fil43,fil44,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve120 : Ban 60 7 etat92 := viaCut proj19 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def fil67 : ℕ := 0x3ffc0000
def etat93 : List ℕ := [fil67,fil43,fil44,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve121 : Ban 60 7 etat93 := viaCut proj21 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat94 : List ℕ := [fil67,fil43,fil44,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve122 : Ban 60 7 etat94 := viaCut proj21 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat95 : List ℕ := [fil52,fil43,fil44,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve123 : Ban 60 7 etat95 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat96 : List ℕ := [fil53,fil43,fil44,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve124 : Ban 60 7 etat96 := viaCut proj18 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat97 : List ℕ := [fil54,fil43,fil44,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve125 : Ban 60 7 etat97 := viaCut proj19 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def fil68 : ℕ := 0xfff000000000
def etat98 : List ℕ := [fil68,fil43,fil44,fil65,fil45,fil46,fil47]
def proj22 : Projection 60 30 := pick [0,1,2,3,5,6,7,8,9,11,12,13,14,15,17,18,19,20,21,23,24,25,26,27,29,30,31,32,33,35] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve126 : Ban 60 7 etat98 := viaCut proj22 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat99 : List ℕ := [fil68,fil43,fil44,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve127 : Ban 60 7 etat99 := viaCut proj22 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat100 : List ℕ := [fil55,fil43,fil44,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve128 : Ban 60 7 etat100 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat101 : List ℕ := [fil56,fil43,fil44,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve129 : Ban 60 7 etat101 := viaCut proj21 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat102 : List ℕ := [fil57,fil43,fil44,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve130 : Ban 60 7 etat102 := viaCut proj18 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat103 : List ℕ := [fil57,fil44,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve131 : Ban 60 7 etat103 := viaCut proj18 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def etat104 : List ℕ := [fil58,fil43,fil44,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve132 : Ban 60 7 etat104 := viaCut proj18 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat105 : List ℕ := [fil58,fil44,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve133 : Ban 60 7 etat105 := viaCut proj18 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def etat106 : List ℕ := [fil59,fil43,fil44,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve134 : Ban 60 7 etat106 := viaCut proj18 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat107 : List ℕ := [fil59,fil44,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve135 : Ban 60 7 etat107 := viaCut proj18 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def etat108 : List ℕ := [fil60,fil43,fil44,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve136 : Ban 60 7 etat108 := viaCut proj18 petit1 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve137 : Ban 60 7 etat78 := viaCut proj18 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat109 : List ℕ := [fil60,fil43,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve138 : Ban 60 7 etat109 := viaCut proj18 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat110 : List ℕ := [fil43,fil61,fil44,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve139 : Ban 60 7 etat110 := viaCut proj19 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat111 : List ℕ := [fil43,fil61,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve140 : Ban 60 7 etat111 := viaCut proj19 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def etat112 : List ℕ := [fil43,fil62,fil44,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve141 : Ban 60 7 etat112 := viaCut proj19 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat113 : List ℕ := [fil43,fil62,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve142 : Ban 60 7 etat113 := viaCut proj19 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def etat114 : List ℕ := [fil43,fil63,fil44,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve143 : Ban 60 7 etat114 := viaCut proj19 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat115 : List ℕ := [fil43,fil63,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve144 : Ban 60 7 etat115 := viaCut proj19 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def etat116 : List ℕ := [fil43,fil64,fil44,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve145 : Ban 60 7 etat116 := viaCut proj19 petit1 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve146 : Ban 60 7 etat82 := viaCut proj19 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat117 : List ℕ := [fil4,fil15,fil0,fil1,fil2,fil3]
def etat118 : List ℕ := [fil4,fil15,fil9,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve149 : Ban 30 4 etat118 := viaSmall (by decide +kernel) (by decide)
def etat119 : List ℕ := [fil4,fil0,fil22,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve150 : Ban 30 4 etat119 := viaSmall (by decide +kernel) (by decide)
def etat120 : List ℕ := [fil15,fil0,fil1,fil2,fil7]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve151 : Ban 30 4 etat120 := viaSmall (by decide +kernel) (by decide)
def etat121 : List ℕ := [fil15,fil0,fil1,fil8,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve152 : Ban 30 4 etat121 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve148 : Ban 30 5 etat117 := viaBranch (ws := [etat118,etat3,etat119,etat23,etat25,etat120,etat121])
  (consBan preuve149 (consBan preuve5 (consBan preuve150 (consBan preuve28 (consBan preuve30 (consBan preuve151 (consBan preuve152 (nilBan _ _))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def etat122 : List ℕ := [fil10,fil15,fil0,fil1,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve153 : Ban 30 5 etat122 := viaPerm proj0 proj0 preuve148 (by decide +kernel) (by decide +kernel)
def etat123 : List ℕ := [fil11,fil15,fil0,fil1,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve154 : Ban 30 5 etat123 := viaSmall (by decide +kernel) (by decide)
def etat124 : List ℕ := [fil12,fil15,fil0,fil1,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve155 : Ban 30 5 etat124 := viaSmall (by decide +kernel) (by decide)
def etat125 : List ℕ := [fil4,fil5,fil6,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve158 : Ban 30 4 etat125 := viaSmall (by decide +kernel) (by decide)
def etat126 : List ℕ := [fil4,fil5,fil1,fil2,fil7]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve159 : Ban 30 4 etat126 := viaSmall (by decide +kernel) (by decide)
def etat127 : List ℕ := [fil4,fil5,fil1,fil8,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve160 : Ban 30 4 etat127 := viaSmall (by decide +kernel) (by decide)
def etat128 : List ℕ := [fil4,fil5,fil9,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve161 : Ban 30 4 etat128 := viaSmall (by decide +kernel) (by decide)
def etat129 : List ℕ := [fil5,fil6,fil1,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve162 : Ban 30 4 etat129 := viaSmall (by decide +kernel) (by decide)
def etat130 : List ℕ := [fil5,fil1,fil2,fil8,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve163 : Ban 30 4 etat130 := viaSmall (by decide +kernel) (by decide)
def etat131 : List ℕ := [fil5,fil1,fil2,fil3,fil7]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve164 : Ban 30 4 etat131 := viaSmall (by decide +kernel) (by decide)
def etat132 : List ℕ := [fil5,fil1,fil2,fil7]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve165 : Ban 30 4 etat132 := viaSmall (by decide +kernel) (by decide)
def etat133 : List ℕ := [fil5,fil1,fil8,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve166 : Ban 30 4 etat133 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve167 : Ban 30 4 etat0 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve157 : Ban 30 5 etat2 := viaBranch (ws := [etat125,etat126,etat127,etat128,etat1,etat7,etat8,etat9,etat129,etat130,etat131,etat132,etat133,etat0])
  (consBan preuve158 (consBan preuve159 (consBan preuve160 (consBan preuve161 (consBan preuve23 (consBan preuve9 (consBan preuve10 (consBan preuve11 (consBan preuve162 (consBan preuve163 (consBan preuve164 (consBan preuve165 (consBan preuve166 (consBan preuve167 (nilBan _ _)))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve156 : Ban 30 5 etat21 := viaPerm proj3 proj4 preuve157 (by decide +kernel) (by decide +kernel)
def etat134 : List ℕ := [fil13,fil15,fil0,fil1,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve168 : Ban 30 5 etat134 := viaSmall (by decide +kernel) (by decide)
def etat135 : List ℕ := [fil14,fil15,fil0,fil1,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve169 : Ban 30 5 etat135 := viaSmall (by decide +kernel) (by decide)
def etat136 : List ℕ := [fil16,fil15,fil0,fil1,fil2,fil3]
def fil69 : ℕ := 0xf83e0
def etat137 : List ℕ := [fil69,fil15,fil1,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve171 : Ban 30 4 etat137 := viaSmall (by decide +kernel) (by decide)
def etat138 : List ℕ := [fil16,fil15,fil1,fil21,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve172 : Ban 30 4 etat138 := viaSmall (by decide +kernel) (by decide)
def etat139 : List ℕ := [fil16,fil0,fil1,fil23,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve173 : Ban 30 4 etat139 := viaSmall (by decide +kernel) (by decide)
def etat140 : List ℕ := [fil16,fil0,fil1,fil2,fil20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve174 : Ban 30 4 etat140 := viaSmall (by decide +kernel) (by decide)
def etat141 : List ℕ := [fil16,fil0,fil1,fil24,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve175 : Ban 30 4 etat141 := viaSmall (by decide +kernel) (by decide)
def fil70 : ℕ := 0x4a5294a7fff801f
def etat142 : List ℕ := [fil15,fil0,fil1,fil2,fil70]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve176 : Ban 30 4 etat142 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve170 : Ban 30 5 etat136 := viaBranch (ws := [etat15,etat137,etat138,etat139,etat140,etat141,etat142])
  (consBan preuve24 (consBan preuve171 (consBan preuve172 (consBan preuve173 (consBan preuve174 (consBan preuve175 (consBan preuve176 (nilBan _ _))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def etat143 : List ℕ := [fil69,fil16,fil1,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve178 : Ban 30 4 etat143 := viaSmall (by decide +kernel) (by decide)
def etat144 : List ℕ := [fil69,fil0,fil1,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve179 : Ban 30 4 etat144 := viaSmall (by decide +kernel) (by decide)
def fil71 : ℕ := 0x84210840000000
def etat145 : List ℕ := [fil71,fil0,fil1,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve180 : Ban 30 4 etat145 := viaSmall (by decide +kernel) (by decide)
def etat146 : List ℕ := [fil16,fil5,fil1,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve181 : Ban 30 4 etat146 := viaSmall (by decide +kernel) (by decide)
def etat147 : List ℕ := [fil16,fil0,fil1,fil2,fil19]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve182 : Ban 30 4 etat147 := viaSmall (by decide +kernel) (by decide)
def etat148 : List ℕ := [fil16,fil0,fil1,fil2,fil70]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve183 : Ban 30 4 etat148 := viaSmall (by decide +kernel) (by decide)
def etat149 : List ℕ := [fil16,fil0,fil1,fil21,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve184 : Ban 30 4 etat149 := viaSmall (by decide +kernel) (by decide)
def etat150 : List ℕ := [fil16,fil1,fil9,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve185 : Ban 30 4 etat150 := viaSmall (by decide +kernel) (by decide)
def fil72 : ℕ := 0x18c6318c1f07c1f
def etat151 : List ℕ := [fil0,fil1,fil72,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve186 : Ban 30 4 etat151 := viaSmall (by decide +kernel) (by decide)
def etat152 : List ℕ := [fil0,fil1,fil2,fil3,fil70]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve187 : Ban 30 4 etat152 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve177 : Ban 30 5 etat22 := viaBranch (ws := [etat1,etat143,etat144,etat145,etat146,etat139,etat147,etat148,etat140,etat141,etat149,etat150,etat10,etat151,etat33,etat152])
  (consBan preuve23 (consBan preuve178 (consBan preuve179 (consBan preuve180 (consBan preuve181 (consBan preuve173 (consBan preuve182 (consBan preuve183 (consBan preuve174 (consBan preuve175 (consBan preuve184 (consBan preuve185 (consBan preuve12 (consBan preuve186 (consBan preuve38 (consBan preuve187 (nilBan _ _)))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def etat153 : List ℕ := [fil17,fil15,fil0,fil1,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve188 : Ban 30 5 etat153 := viaPerm proj0 proj0 preuve170 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve189 : Ban 30 5 etat23 := viaPerm proj0 proj0 preuve177 (by decide +kernel) (by decide +kernel)
def etat154 : List ℕ := [fil15,fil18,fil0,fil1,fil2,fil3]
def etat155 : List ℕ := [fil15,fil18,fil1,fil23,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve191 : Ban 30 4 etat155 := viaSmall (by decide +kernel) (by decide)
def etat156 : List ℕ := [fil15,fil18,fil1,fil2,fil19]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve192 : Ban 30 4 etat156 := viaSmall (by decide +kernel) (by decide)
def etat157 : List ℕ := [fil15,fil18,fil1,fil2,fil20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve193 : Ban 30 4 etat157 := viaSmall (by decide +kernel) (by decide)
def etat158 : List ℕ := [fil15,fil18,fil1,fil21,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve194 : Ban 30 4 etat158 := viaSmall (by decide +kernel) (by decide)
def etat159 : List ℕ := [fil18,fil0,fil1,fil23,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve195 : Ban 30 4 etat159 := viaSmall (by decide +kernel) (by decide)
def etat160 : List ℕ := [fil18,fil0,fil1,fil24,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve196 : Ban 30 4 etat160 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve190 : Ban 30 5 etat154 := viaBranch (ws := [etat15,etat17,etat22,etat155,etat156,etat157,etat158,etat26,etat142,etat159,etat160])
  (consBan preuve24 (consBan preuve26 (consBan preuve27 (consBan preuve191 (consBan preuve192 (consBan preuve193 (consBan preuve194 (consBan preuve31 (consBan preuve176 (consBan preuve195 (consBan preuve196 (nilBan _ _))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def etat161 : List ℕ := [fil10,fil18,fil1,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve198 : Ban 30 4 etat161 := viaSmall (by decide +kernel) (by decide)
def etat162 : List ℕ := [fil17,fil18,fil1,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve199 : Ban 30 4 etat162 := viaSmall (by decide +kernel) (by decide)
def fil73 : ℕ := 0x842108400f8000
def etat163 : List ℕ := [fil15,fil73,fil1,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve200 : Ban 30 4 etat163 := viaSmall (by decide +kernel) (by decide)
def etat164 : List ℕ := [fil15,fil18,fil1,fil2,fil70]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve201 : Ban 30 4 etat164 := viaSmall (by decide +kernel) (by decide)
def etat165 : List ℕ := [fil15,fil18,fil1,fil24,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve202 : Ban 30 4 etat165 := viaSmall (by decide +kernel) (by decide)
def fil74 : ℕ := 0x18c6318c1fffc1f
def etat166 : List ℕ := [fil15,fil1,fil74,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve203 : Ban 30 4 etat166 := viaSmall (by decide +kernel) (by decide)
def etat167 : List ℕ := [fil18,fil1,fil22,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve204 : Ban 30 4 etat167 := viaSmall (by decide +kernel) (by decide)
def etat168 : List ℕ := [fil18,fil1,fil23,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve205 : Ban 30 4 etat168 := viaSmall (by decide +kernel) (by decide)
def etat169 : List ℕ := [fil18,fil1,fil2,fil3,fil20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve206 : Ban 30 4 etat169 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve197 : Ban 30 5 etat24 := viaBranch (ws := [etat161,etat21,etat162,etat163,etat155,etat156,etat164,etat157,etat165,etat158,etat20,etat166,etat29,etat30,etat35,etat167,etat168,etat169,etat0])
  (consBan preuve198 (consBan preuve25 (consBan preuve199 (consBan preuve200 (consBan preuve191 (consBan preuve192 (consBan preuve201 (consBan preuve193 (consBan preuve202 (consBan preuve194 (consBan preuve97 (consBan preuve203 (consBan preuve34 (consBan preuve35 (consBan preuve98 (consBan preuve204 (consBan preuve205 (consBan preuve206 (consBan preuve167 (nilBan _ _))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def etat170 : List ℕ := [fil15,fil5,fil0,fil1,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve207 : Ban 30 5 etat170 := viaPerm proj0 proj0 preuve190 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve208 : Ban 30 5 etat25 := viaPerm proj0 proj0 preuve197 (by decide +kernel) (by decide +kernel)
def etat171 : List ℕ := [fil15,fil0,fil25,fil1,fil2,fil3]
def etat172 : List ℕ := [fil15,fil25,fil9,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve210 : Ban 30 4 etat172 := viaSmall (by decide +kernel) (by decide)
def fil75 : ℕ := 0x18c6318c00fffff
def etat173 : List ℕ := [fil15,fil1,fil75,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve211 : Ban 30 4 etat173 := viaSmall (by decide +kernel) (by decide)
def fil76 : ℕ := 0x108421080007c00
def etat174 : List ℕ := [fil0,fil76,fil1,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve212 : Ban 30 4 etat174 := viaSmall (by decide +kernel) (by decide)
def etat175 : List ℕ := [fil0,fil25,fil6,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve213 : Ban 30 4 etat175 := viaSmall (by decide +kernel) (by decide)
def etat176 : List ℕ := [fil0,fil25,fil22,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve214 : Ban 30 4 etat176 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve209 : Ban 30 5 etat171 := viaBranch (ws := [etat1,etat23,etat25,etat172,etat173,etat174,etat175,etat176,etat45])
  (consBan preuve23 (consBan preuve28 (consBan preuve30 (consBan preuve210 (consBan preuve211 (consBan preuve212 (consBan preuve213 (consBan preuve214 (consBan preuve52 (nilBan _ _))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def etat177 : List ℕ := [fil15,fil0,fil26,fil1,fil2,fil3]
def etat178 : List ℕ := [fil15,fil26,fil9,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve216 : Ban 30 4 etat178 := viaSmall (by decide +kernel) (by decide)
def fil77 : ℕ := 0x18c6318c1ff83ff
def etat179 : List ℕ := [fil15,fil1,fil77,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve217 : Ban 30 4 etat179 := viaSmall (by decide +kernel) (by decide)
def fil78 : ℕ := 0x108421081f00000
def etat180 : List ℕ := [fil0,fil78,fil1,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve218 : Ban 30 4 etat180 := viaSmall (by decide +kernel) (by decide)
def etat181 : List ℕ := [fil0,fil26,fil6,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve219 : Ban 30 4 etat181 := viaSmall (by decide +kernel) (by decide)
def etat182 : List ℕ := [fil0,fil26,fil22,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve220 : Ban 30 4 etat182 := viaSmall (by decide +kernel) (by decide)
def fil79 : ℕ := 0x18c6318c1f003ff
def etat183 : List ℕ := [fil0,fil1,fil79,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve221 : Ban 30 4 etat183 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve215 : Ban 30 5 etat177 := viaBranch (ws := [etat1,etat23,etat25,etat178,etat179,etat180,etat181,etat182,etat183])
  (consBan preuve23 (consBan preuve28 (consBan preuve30 (consBan preuve216 (consBan preuve217 (consBan preuve218 (consBan preuve219 (consBan preuve220 (consBan preuve221 (nilBan _ _))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def etat184 : List ℕ := [fil15,fil0,fil6,fil1,fil2,fil3]
def etat185 : List ℕ := [fil17,fil0,fil6,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve223 : Ban 30 4 etat185 := viaSmall (by decide +kernel) (by decide)
def etat186 : List ℕ := [fil15,fil5,fil6,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve224 : Ban 30 4 etat186 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve222 : Ban 30 5 etat184 := viaBranch (ws := [etat3,etat185,etat186,etat28,etat31])
  (consBan preuve5 (consBan preuve223 (consBan preuve224 (consBan preuve33 (consBan preuve36 (nilBan _ _))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def etat187 : List ℕ := [fil15,fil0,fil1,fil22,fil2,fil3]
def etat188 : List ℕ := [fil17,fil0,fil22,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve226 : Ban 30 4 etat188 := viaSmall (by decide +kernel) (by decide)
def etat189 : List ℕ := [fil15,fil5,fil22,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve227 : Ban 30 4 etat189 := viaSmall (by decide +kernel) (by decide)
def etat190 : List ℕ := [fil0,fil1,fil22,fil2,fil20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve228 : Ban 30 4 etat190 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve225 : Ban 30 5 etat187 := viaBranch (ws := [etat119,etat21,etat188,etat189,etat28,etat10,etat190])
  (consBan preuve150 (consBan preuve25 (consBan preuve226 (consBan preuve227 (consBan preuve33 (consBan preuve12 (consBan preuve228 (nilBan _ _))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def etat191 : List ℕ := [fil15,fil0,fil1,fil9,fil2,fil3]
def etat192 : List ℕ := [fil17,fil0,fil9,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve230 : Ban 30 4 etat192 := viaSmall (by decide +kernel) (by decide)
def etat193 : List ℕ := [fil15,fil5,fil9,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve231 : Ban 30 4 etat193 := viaSmall (by decide +kernel) (by decide)
def etat194 : List ℕ := [fil15,fil1,fil9,fil2,fil19]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve232 : Ban 30 4 etat194 := viaSmall (by decide +kernel) (by decide)
def etat195 : List ℕ := [fil15,fil1,fil9,fil2,fil20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve233 : Ban 30 4 etat195 := viaSmall (by decide +kernel) (by decide)
def fil80 : ℕ := 0x108421081fffc00
def etat196 : List ℕ := [fil0,fil1,fil80,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve234 : Ban 30 4 etat196 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve229 : Ban 30 5 etat191 := viaBranch (ws := [etat118,etat6,etat192,etat193,etat194,etat195,etat196])
  (consBan preuve149 (consBan preuve8 (consBan preuve230 (consBan preuve231 (consBan preuve232 (consBan preuve233 (consBan preuve234 (nilBan _ _))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def etat197 : List ℕ := [fil15,fil0,fil1,fil37,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve235 : Ban 30 5 etat197 := viaPerm proj0 proj0 preuve209 (by decide +kernel) (by decide +kernel)
def etat198 : List ℕ := [fil15,fil0,fil1,fil38,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve236 : Ban 30 5 etat198 := viaPerm proj0 proj0 preuve215 (by decide +kernel) (by decide +kernel)
def etat199 : List ℕ := [fil15,fil0,fil1,fil23,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve237 : Ban 30 5 etat199 := viaPerm proj0 proj0 preuve222 (by decide +kernel) (by decide +kernel)
def etat200 : List ℕ := [fil15,fil0,fil1,fil2,fil24,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve238 : Ban 30 5 etat200 := viaPerm proj0 proj0 preuve225 (by decide +kernel) (by decide +kernel)
def etat201 : List ℕ := [fil15,fil0,fil1,fil2,fil21,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve239 : Ban 30 5 etat201 := viaPerm proj0 proj0 preuve229 (by decide +kernel) (by decide +kernel)
def etat202 : List ℕ := [fil15,fil0,fil1,fil2,fil35,fil3]
def fil81 : ℕ := 0x3ff
def etat203 : List ℕ := [fil81,fil0,fil1,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve241 : Ban 30 4 etat203 := viaSmall (by decide +kernel) (by decide)
def etat204 : List ℕ := [fil11,fil15,fil0,fil35,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve242 : Ban 30 4 etat204 := viaSmall (by decide +kernel) (by decide)
def fil82 : ℕ := 0x3ff00000
def etat205 : List ℕ := [fil82,fil15,fil0,fil1,fil2]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve243 : Ban 30 4 etat205 := viaSmall (by decide +kernel) (by decide)
def fil83 : ℕ := 0x318c63180007fff
def etat206 : List ℕ := [fil15,fil0,fil1,fil2,fil83]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve244 : Ban 30 4 etat206 := viaSmall (by decide +kernel) (by decide)
def etat207 : List ℕ := [fil15,fil1,fil2,fil32,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve245 : Ban 30 4 etat207 := viaSmall (by decide +kernel) (by decide)
def etat208 : List ℕ := [fil15,fil1,fil21,fil35,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve246 : Ban 30 4 etat208 := viaSmall (by decide +kernel) (by decide)
def etat209 : List ℕ := [fil15,fil9,fil2,fil35,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve247 : Ban 30 4 etat209 := viaSmall (by decide +kernel) (by decide)
def etat210 : List ℕ := [fil0,fil6,fil2,fil35,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve248 : Ban 30 4 etat210 := viaSmall (by decide +kernel) (by decide)
def etat211 : List ℕ := [fil0,fil1,fil23,fil35,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve249 : Ban 30 4 etat211 := viaSmall (by decide +kernel) (by decide)
def fil84 : ℕ := 0x318c631bff07c00
def etat212 : List ℕ := [fil0,fil1,fil2,fil84,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve250 : Ban 30 4 etat212 := viaSmall (by decide +kernel) (by decide)
def fil85 : ℕ := 0x39ce739fff07fff
def etat213 : List ℕ := [fil0,fil1,fil2,fil85,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve251 : Ban 30 4 etat213 := viaSmall (by decide +kernel) (by decide)
def etat214 : List ℕ := [fil0,fil1,fil24,fil35,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve252 : Ban 30 4 etat214 := viaSmall (by decide +kernel) (by decide)
def etat215 : List ℕ := [fil0,fil22,fil2,fil35,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve253 : Ban 30 4 etat215 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve240 : Ban 30 5 etat202 := viaBranch (ws := [etat203,etat204,etat205,etat145,etat163,etat206,etat207,etat208,etat209,etat210,etat211,etat212,etat213,etat214,etat215])
  (consBan preuve241 (consBan preuve242 (consBan preuve243 (consBan preuve180 (consBan preuve200 (consBan preuve244 (consBan preuve245 (consBan preuve246 (consBan preuve247 (consBan preuve248 (consBan preuve249 (consBan preuve250 (consBan preuve251 (consBan preuve252 (consBan preuve253 (nilBan _ _))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def etat216 : List ℕ := [fil15,fil0,fil1,fil2,fil39,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve254 : Ban 30 5 etat216 := viaPerm proj12 proj11 preuve222 (by decide +kernel) (by decide +kernel)
def etat217 : List ℕ := [fil15,fil0,fil1,fil2,fil40,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve255 : Ban 30 5 etat217 := viaPerm proj15 proj16 preuve222 (by decide +kernel) (by decide +kernel)
def etat218 : List ℕ := [fil12,fil15,fil1,fil2,fil19]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve257 : Ban 30 4 etat218 := viaSmall (by decide +kernel) (by decide)
def etat219 : List ℕ := [fil12,fil0,fil1,fil2,fil19]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve258 : Ban 30 4 etat219 := viaSmall (by decide +kernel) (by decide)
def etat220 : List ℕ := [fil17,fil0,fil1,fil2,fil19]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve259 : Ban 30 4 etat220 := viaSmall (by decide +kernel) (by decide)
def etat221 : List ℕ := [fil15,fil5,fil1,fil2,fil19]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve260 : Ban 30 4 etat221 := viaSmall (by decide +kernel) (by decide)
def fil86 : ℕ := 0x4a5294a7ff003ff
def etat222 : List ℕ := [fil15,fil0,fil1,fil2,fil86]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve261 : Ban 30 4 etat222 := viaSmall (by decide +kernel) (by decide)
def etat223 : List ℕ := [fil15,fil1,fil2,fil21,fil19]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve262 : Ban 30 4 etat223 := viaSmall (by decide +kernel) (by decide)
def etat224 : List ℕ := [fil15,fil1,fil2,fil19,fil20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve263 : Ban 30 4 etat224 := viaSmall (by decide +kernel) (by decide)
def etat225 : List ℕ := [fil0,fil1,fil22,fil2,fil19]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve264 : Ban 30 4 etat225 := viaSmall (by decide +kernel) (by decide)
def etat226 : List ℕ := [fil0,fil1,fil2,fil24,fil19]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve265 : Ban 30 4 etat226 := viaSmall (by decide +kernel) (by decide)
def etat227 : List ℕ := [fil0,fil1,fil2,fil19,fil86]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve266 : Ban 30 4 etat227 := viaSmall (by decide +kernel) (by decide)
def etat228 : List ℕ := [fil0,fil1,fil2,fil86]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve267 : Ban 30 4 etat228 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve256 : Ban 30 5 etat26 := viaBranch (ws := [etat218,etat219,etat147,etat220,etat156,etat221,etat222,etat27,etat194,etat223,etat224,etat225,etat226,etat227,etat228])
  (consBan preuve257 (consBan preuve258 (consBan preuve182 (consBan preuve259 (consBan preuve192 (consBan preuve260 (consBan preuve261 (consBan preuve32 (consBan preuve232 (consBan preuve262 (consBan preuve263 (consBan preuve264 (consBan preuve265 (consBan preuve266 (consBan preuve267 (nilBan _ _))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def etat229 : List ℕ := [fil15,fil0,fil1,fil2,fil19,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve268 : Ban 30 5 etat229 := viaSmall (by decide +kernel) (by decide)
def etat230 : List ℕ := [fil15,fil0,fil1,fil2,fil3,fil20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve269 : Ban 30 5 etat230 := viaSmall (by decide +kernel) (by decide)
def etat231 : List ℕ := [fil15,fil0,fil1,fil2,fil3,fil36]
def fil87 : ℕ := 0xf801f
def etat232 : List ℕ := [fil87,fil15,fil1,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve271 : Ban 30 4 etat232 := viaSmall (by decide +kernel) (by decide)
def etat233 : List ℕ := [fil13,fil15,fil0,fil2,fil36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve272 : Ban 30 4 etat233 := viaSmall (by decide +kernel) (by decide)
def etat234 : List ℕ := [fil15,fil1,fil2,fil19,fil36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve273 : Ban 30 4 etat234 := viaSmall (by decide +kernel) (by decide)
def fil88 : ℕ := 0x5294a52bff07c00
def etat235 : List ℕ := [fil15,fil1,fil2,fil3,fil88]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve274 : Ban 30 4 etat235 := viaSmall (by decide +kernel) (by decide)
def etat236 : List ℕ := [fil15,fil9,fil2,fil3,fil36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve275 : Ban 30 4 etat236 := viaSmall (by decide +kernel) (by decide)
def etat237 : List ℕ := [fil0,fil6,fil2,fil3,fil36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve276 : Ban 30 4 etat237 := viaSmall (by decide +kernel) (by decide)
def fil89 : ℕ := 0x5294a52bffffc00
def etat238 : List ℕ := [fil0,fil1,fil2,fil3,fil89]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve277 : Ban 30 4 etat238 := viaSmall (by decide +kernel) (by decide)
def etat239 : List ℕ := [fil0,fil1,fil2,fil20,fil36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve278 : Ban 30 4 etat239 := viaSmall (by decide +kernel) (by decide)
def etat240 : List ℕ := [fil0,fil22,fil2,fil3,fil36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve279 : Ban 30 4 etat240 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve270 : Ban 30 5 etat231 := viaBranch (ws := [etat1,etat232,etat233,etat23,etat234,etat235,etat236,etat237,etat238,etat50,etat239,etat240])
  (consBan preuve23 (consBan preuve271 (consBan preuve272 (consBan preuve28 (consBan preuve273 (consBan preuve274 (consBan preuve275 (consBan preuve276 (consBan preuve277 (consBan preuve57 (consBan preuve278 (consBan preuve279 (nilBan _ _)))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def etat241 : List ℕ := [fil15,fil0,fil1,fil2,fil3,fil41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve280 : Ban 30 5 etat241 := viaPerm proj0 proj0 preuve270 (by decide +kernel) (by decide +kernel)
def etat242 : List ℕ := [fil12,fil15,fil1,fil2,fil20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve282 : Ban 30 4 etat242 := viaSmall (by decide +kernel) (by decide)
def etat243 : List ℕ := [fil12,fil0,fil1,fil2,fil20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve283 : Ban 30 4 etat243 := viaSmall (by decide +kernel) (by decide)
def etat244 : List ℕ := [fil12,fil1,fil2,fil20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve284 : Ban 30 4 etat244 := viaSmall (by decide +kernel) (by decide)
def etat245 : List ℕ := [fil17,fil0,fil1,fil2,fil20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve285 : Ban 30 4 etat245 := viaSmall (by decide +kernel) (by decide)
def etat246 : List ℕ := [fil15,fil5,fil1,fil2,fil20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve286 : Ban 30 4 etat246 := viaSmall (by decide +kernel) (by decide)
def etat247 : List ℕ := [fil15,fil1,fil2,fil21,fil20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve287 : Ban 30 4 etat247 := viaSmall (by decide +kernel) (by decide)
def etat248 : List ℕ := [fil0,fil1,fil2,fil24,fil20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve288 : Ban 30 4 etat248 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve281 : Ban 30 5 etat27 := viaBranch (ws := [etat242,etat243,etat244,etat140,etat245,etat157,etat246,etat26,etat20,etat195,etat247,etat224,etat190,etat248,etat0,etat34])
  (consBan preuve282 (consBan preuve283 (consBan preuve284 (consBan preuve174 (consBan preuve285 (consBan preuve193 (consBan preuve286 (consBan preuve31 (consBan preuve97 (consBan preuve233 (consBan preuve287 (consBan preuve263 (consBan preuve228 (consBan preuve288 (consBan preuve167 (consBan preuve39 (nilBan _ _)))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def etat249 : List ℕ := [fil28,fil15,fil1,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve290 : Ban 30 4 etat249 := viaSmall (by decide +kernel) (by decide)
def etat250 : List ℕ := [fil17,fil15,fil9,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve291 : Ban 30 4 etat250 := viaSmall (by decide +kernel) (by decide)
def etat251 : List ℕ := [fil15,fil1,fil80,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve292 : Ban 30 4 etat251 := viaSmall (by decide +kernel) (by decide)
def etat252 : List ℕ := [fil15,fil1,fil30,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve293 : Ban 30 4 etat252 := viaSmall (by decide +kernel) (by decide)
def etat253 : List ℕ := [fil15,fil1,fil2,fil33,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve294 : Ban 30 4 etat253 := viaSmall (by decide +kernel) (by decide)
def etat254 : List ℕ := [fil1,fil80,fil9,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve295 : Ban 30 4 etat254 := viaSmall (by decide +kernel) (by decide)
def etat255 : List ℕ := [fil1,fil9,fil2,fil24,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve296 : Ban 30 4 etat255 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve289 : Ban 30 5 etat28 := viaBranch (ws := [etat118,etat7,etat8,etat249,etat150,etat250,etat25,etat193,etat172,etat178,etat251,etat252,etat195,etat207,etat253,etat209,etat236,etat53,etat254,etat255,etat55])
  (consBan preuve149 (consBan preuve9 (consBan preuve10 (consBan preuve290 (consBan preuve185 (consBan preuve291 (consBan preuve30 (consBan preuve231 (consBan preuve210 (consBan preuve216 (consBan preuve292 (consBan preuve293 (consBan preuve233 (consBan preuve245 (consBan preuve294 (consBan preuve247 (consBan preuve275 (consBan preuve60 (consBan preuve295 (consBan preuve296 (consBan preuve62 (nilBan _ _))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve297 : Ban 30 5 etat29 := viaPerm proj0 proj0 preuve289 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve298 : Ban 30 5 etat30 := viaPerm proj17 proj17 preuve256 (by decide +kernel) (by decide +kernel)
def etat256 : List ℕ := [fil0,fil1,fil75,fil2,fil3]
def etat257 : List ℕ := [fil4,fil1,fil75,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve301 : Ban 30 4 etat257 := viaSmall (by decide +kernel) (by decide)
def etat258 : List ℕ := [fil18,fil1,fil75,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve302 : Ban 30 4 etat258 := viaSmall (by decide +kernel) (by decide)
def etat259 : List ℕ := [fil0,fil26,fil75,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve303 : Ban 30 4 etat259 := viaSmall (by decide +kernel) (by decide)
def fil90 : ℕ := 0x18c6318c00f801f
def etat260 : List ℕ := [fil0,fil1,fil90,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve304 : Ban 30 4 etat260 := viaSmall (by decide +kernel) (by decide)
def etat261 : List ℕ := [fil0,fil1,fil75,fil2,fil40]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve305 : Ban 30 4 etat261 := viaSmall (by decide +kernel) (by decide)
def etat262 : List ℕ := [fil0,fil1,fil75,fil2,fil36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve306 : Ban 30 4 etat262 := viaSmall (by decide +kernel) (by decide)
def fil91 : ℕ := 0x39ce739fe0fffff
def etat263 : List ℕ := [fil0,fil1,fil2,fil91,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve307 : Ban 30 4 etat263 := viaSmall (by decide +kernel) (by decide)
def etat264 : List ℕ := [fil0,fil75,fil2,fil35,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve308 : Ban 30 4 etat264 := viaSmall (by decide +kernel) (by decide)
def etat265 : List ℕ := [fil76,fil1,fil75,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve309 : Ban 30 4 etat265 := viaSmall (by decide +kernel) (by decide)
def etat266 : List ℕ := [fil6,fil1,fil75,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve310 : Ban 30 4 etat266 := viaSmall (by decide +kernel) (by decide)
def etat267 : List ℕ := [fil1,fil75,fil2,fil21,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve311 : Ban 30 4 etat267 := viaSmall (by decide +kernel) (by decide)
def etat268 : List ℕ := [fil1,fil75,fil2,fil3,fil20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve312 : Ban 30 4 etat268 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve300 : Ban 30 5 etat256 := viaBranch (ws := [etat257,etat39,etat17,etat18,etat173,etat258,etat9,etat174,etat36,etat259,etat45,etat260,etat261,etat262,etat38,etat47,etat263,etat62,etat50,etat264,etat265,etat266,etat267,etat268])
  (consBan preuve301 (consBan preuve46 (consBan preuve26 (consBan preuve95 (consBan preuve211 (consBan preuve302 (consBan preuve11 (consBan preuve212 (consBan preuve99 (consBan preuve303 (consBan preuve52 (consBan preuve304 (consBan preuve305 (consBan preuve306 (consBan preuve101 (consBan preuve54 (consBan preuve307 (consBan preuve108 (consBan preuve57 (consBan preuve308 (consBan preuve309 (consBan preuve310 (consBan preuve311 (consBan preuve312 (nilBan _ _)))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve299 : Ban 30 5 etat31 := viaPerm proj9 proj9 preuve300 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve313 : Ban 30 5 etat33 := viaPerm proj2 proj1 preuve300 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve147 : Ban 30 6 etat20 := viaBranch (ws := [etat117,etat1,etat122,etat15,etat123,etat124,etat21,etat17,etat134,etat135,etat136,etat22,etat153,etat23,etat154,etat24,etat170,etat25,etat171,etat177,etat184,etat187,etat191,etat197,etat198,etat199,etat200,etat201,etat202,etat216,etat217,etat26,etat229,etat230,etat231,etat241,etat27,etat28,etat29,etat30,etat10,etat31,etat32,etat33,etat34])
  (consBan preuve148 (consBan preuve3 (consBan preuve153 (consBan preuve17 (consBan preuve154 (consBan preuve155 (consBan preuve156 (consBan preuve19 (consBan preuve168 (consBan preuve169 (consBan preuve170 (consBan preuve177 (consBan preuve188 (consBan preuve189 (consBan preuve190 (consBan preuve197 (consBan preuve207 (consBan preuve208 (consBan preuve209 (consBan preuve215 (consBan preuve222 (consBan preuve225 (consBan preuve229 (consBan preuve235 (consBan preuve236 (consBan preuve237 (consBan preuve238 (consBan preuve239 (consBan preuve240 (consBan preuve254 (consBan preuve255 (consBan preuve256 (consBan preuve268 (consBan preuve269 (consBan preuve270 (consBan preuve280 (consBan preuve281 (consBan preuve289 (consBan preuve297 (consBan preuve298 (consBan preuve44 (consBan preuve299 (consBan preuve65 (consBan preuve313 (consBan preuve71 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit3 : Wide 30 6 etat20 := viaSub (ws := [etat0,etat20])
  (consBan preuve2 (consBan preuve147 (nilBan _ _)))
  (by decide) (by decide +kernel)
def fil92 : ℕ := 0xc30c30c30c30c300000003fffffff
def etat269 : List ℕ := [fil43,fil44,fil92,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve314 : Ban 60 7 etat269 := viaCut proj18 petit3 (by decide) (by decide +kernel) (by decide +kernel)
def etat270 : List ℕ := [fil43,fil44,fil92,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve315 : Ban 60 7 etat270 := viaCut proj18 petit3 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve316 : Ban 30 6 etat35 := viaPerm proj8 proj8 preuve147 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit4 : Wide 30 6 etat35 := viaSub (ws := [etat0,etat35])
  (consBan preuve2 (consBan preuve316 (nilBan _ _)))
  (by decide) (by decide +kernel)
def fil93 : ℕ := 0xc30c30c30c30c3000fff00003ffff
def etat271 : List ℕ := [fil43,fil44,fil93,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve317 : Ban 60 7 etat271 := viaCut proj18 petit4 (by decide) (by decide +kernel) (by decide +kernel)
def etat272 : List ℕ := [fil43,fil44,fil93,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve318 : Ban 60 7 etat272 := viaCut proj18 petit4 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve319 : Ban 30 6 etat9 := viaPerm proj4 proj3 preuve147 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit5 : Wide 30 6 etat9 := viaSub (ws := [etat0,etat9])
  (consBan preuve2 (consBan preuve319 (nilBan _ _)))
  (by decide) (by decide +kernel)
def fil94 : ℕ := 0xc30c30c30c30c3000fff03ffc003f
def etat273 : List ℕ := [fil43,fil44,fil94,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve320 : Ban 60 7 etat273 := viaCut proj18 petit5 (by decide) (by decide +kernel) (by decide +kernel)
def etat274 : List ℕ := [fil43,fil44,fil94,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve321 : Ban 60 7 etat274 := viaCut proj18 petit5 (by decide) (by decide +kernel) (by decide +kernel)
def fil95 : ℕ := 0x104104104104104000000fc003ffc0
def etat275 : List ℕ := [fil43,fil44,fil65,fil95,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve322 : Ban 60 7 etat275 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def fil96 : ℕ := 0x10410410410410403f00000003ffc0
def etat276 : List ℕ := [fil43,fil44,fil65,fil96,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve323 : Ban 60 7 etat276 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def fil97 : ℕ := 0x10410410410410403f000fc0000000
def etat277 : List ℕ := [fil43,fil44,fil65,fil97,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve324 : Ban 60 7 etat277 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def fil98 : ℕ := 0x10410410410410403f000fc0000fc0
def etat278 : List ℕ := [fil43,fil44,fil65,fil98,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve325 : Ban 60 7 etat278 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def fil99 : ℕ := 0x10410410410410403f000fc003f000
def etat279 : List ℕ := [fil43,fil44,fil65,fil99,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve326 : Ban 60 7 etat279 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def fil100 : ℕ := 0x14514514514514503f03ffc0ffffff
def etat280 : List ℕ := [fil43,fil44,fil65,fil45,fil100,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve327 : Ban 60 7 etat280 := viaCut proj18 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def fil101 : ℕ := 0x18618618618618603ffc0fff03ffff
def etat281 : List ℕ := [fil43,fil44,fil65,fil45,fil101,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve328 : Ban 60 7 etat281 := viaCut proj19 petit0 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit6 : Wide 30 4 etat38 := viaSearch (by decide +kernel)
def fil102 : ℕ := 0x1c71c71c71c71c703fffffffffffff
def etat282 : List ℕ := [fil42,fil43,fil65,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve330 : Ban 60 6 etat282 := viaCut proj18 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def etat283 : List ℕ := [fil42,fil44,fil65,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve331 : Ban 60 6 etat283 := viaCut proj19 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def etat284 : List ℕ := [fil42,fil65,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve332 : Ban 60 6 etat284 := viaCut proj18 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat285 : List ℕ := [fil66,fil43,fil44,fil65,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve333 : Ban 60 6 etat285 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat286 : List ℕ := [fil66,fil43,fil44,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve334 : Ban 60 6 etat286 := viaCut proj20 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def etat287 : List ℕ := [fil66,fil43,fil44,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve335 : Ban 60 6 etat287 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit7 : Wide 30 4 etat48 := viaSearch (by decide +kernel)
def etat288 : List ℕ := [fil67,fil43,fil44,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve336 : Ban 60 6 etat288 := viaCut proj21 petit7 (by decide) (by decide +kernel) (by decide +kernel)
def fil103 : ℕ := 0xffffc0000
def etat289 : List ℕ := [fil103,fil43,fil44,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve337 : Ban 60 6 etat289 := viaCut proj21 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def etat290 : List ℕ := [fil68,fil43,fil44,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve338 : Ban 60 6 etat290 := viaCut proj22 petit7 (by decide) (by decide +kernel) (by decide +kernel)
def fil104 : ℕ := 0x3ffff000000000
def etat291 : List ℕ := [fil104,fil43,fil44,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve339 : Ban 60 6 etat291 := viaCut proj22 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def etat292 : List ℕ := [fil57,fil44,fil65,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve340 : Ban 60 6 etat292 := viaCut proj18 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat293 : List ℕ := [fil58,fil44,fil65,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve341 : Ban 60 6 etat293 := viaCut proj18 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat294 : List ℕ := [fil59,fil44,fil65,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve342 : Ban 60 6 etat294 := viaCut proj18 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat295 : List ℕ := [fil60,fil43,fil44,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve343 : Ban 60 6 etat295 := viaCut proj18 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def etat296 : List ℕ := [fil60,fil43,fil65,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve344 : Ban 60 6 etat296 := viaCut proj18 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def etat297 : List ℕ := [fil43,fil61,fil65,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve345 : Ban 60 6 etat297 := viaCut proj19 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat298 : List ℕ := [fil43,fil62,fil65,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve346 : Ban 60 6 etat298 := viaCut proj19 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat299 : List ℕ := [fil43,fil63,fil65,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve347 : Ban 60 6 etat299 := viaCut proj19 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat300 : List ℕ := [fil43,fil64,fil44,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve348 : Ban 60 6 etat300 := viaCut proj19 petit6 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit8 : Wide 30 5 etat191 := viaSub (ws := [etat0,etat20,etat28,etat38,etat191])
  (consBan preuve93 (consBan preuve22 (consBan preuve289 (consBan preuve45 (consBan preuve229 (nilBan _ _))))))
  (by decide) (by decide +kernel)
def etat301 : List ℕ := [fil43,fil44,fil92,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve349 : Ban 60 6 etat301 := viaCut proj18 petit8 (by decide) (by decide +kernel) (by decide +kernel)
def etat302 : List ℕ := [fil18,fil0,fil1,fil9,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve350 : Ban 30 5 etat41 := viaPerm proj8 proj8 preuve289 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve351 : Ban 30 5 etat302 := viaPerm proj8 proj8 preuve229 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit9 : Wide 30 5 etat302 := viaSub (ws := [etat0,etat35,etat41,etat38,etat302])
  (consBan preuve93 (consBan preuve40 (consBan preuve350 (consBan preuve45 (consBan preuve351 (nilBan _ _))))))
  (by decide) (by decide +kernel)
def etat303 : List ℕ := [fil43,fil44,fil93,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve352 : Ban 60 6 etat303 := viaCut proj18 petit9 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit10 : Wide 30 5 etat9 := viaSub (ws := [etat0,etat9])
  (consBan preuve93 (consBan preuve41 (nilBan _ _)))
  (by decide) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve353 : Ban 60 6 etat273 := viaCut proj18 petit10 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve354 : Ban 30 5 etat42 := viaPerm proj4 proj3 preuve281 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit11 : Wide 30 5 etat42 := viaSub (ws := [etat42])
  (consBan preuve354 (nilBan _ _))
  (by decide) (by decide +kernel)
def etat304 : List ℕ := [fil43,fil44,fil94,fil65,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve355 : Ban 60 6 etat304 := viaCut proj18 petit11 (by decide) (by decide +kernel) (by decide +kernel)
def etat305 : List ℕ := [fil43,fil44,fil94,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve356 : Ban 60 6 etat305 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat306 : List ℕ := [fil43,fil44,fil94,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve357 : Ban 60 6 etat306 := viaCut proj18 petit11 (by decide) (by decide +kernel) (by decide +kernel)
def etat307 : List ℕ := [fil43,fil44,fil65,fil95,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve358 : Ban 60 6 etat307 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat308 : List ℕ := [fil43,fil44,fil65,fil96,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve359 : Ban 60 6 etat308 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve360 : Ban 60 6 etat277 := viaCut proj20 petit6 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit12 : Wide 30 5 etat10 := viaSub (ws := [etat0,etat10])
  (consBan preuve93 (consBan preuve44 (nilBan _ _)))
  (by decide) (by decide +kernel)
def fil105 : ℕ := 0x14514514514514503f03ffc0fc0fc0
def etat309 : List ℕ := [fil43,fil44,fil65,fil45,fil105,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve361 : Ban 60 6 etat309 := viaCut proj18 petit12 (by decide) (by decide +kernel) (by decide +kernel)
def fil106 : ℕ := 0x18618618618618603ffc0fff03f000
def etat310 : List ℕ := [fil43,fil44,fil65,fil45,fil106,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve362 : Ban 60 6 etat310 := viaCut proj19 petit12 (by decide) (by decide +kernel) (by decide +kernel)
def etat311 : List ℕ := [fil14,fil0,fil1,fil29,fil2]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve364 : Ban 30 4 etat311 := viaSmall (by decide +kernel) (by decide)
def etat312 : List ℕ := [fil18,fil1,fil29,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve365 : Ban 30 4 etat312 := viaSmall (by decide +kernel) (by decide)
def etat313 : List ℕ := [fil0,fil26,fil29,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve366 : Ban 30 4 etat313 := viaSmall (by decide +kernel) (by decide)
def fil107 : ℕ := 0x18c6318c000001f
def etat314 : List ℕ := [fil0,fil1,fil107,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve367 : Ban 30 4 etat314 := viaSmall (by decide +kernel) (by decide)
def etat315 : List ℕ := [fil0,fil1,fil29,fil37,fil2]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve368 : Ban 30 4 etat315 := viaSmall (by decide +kernel) (by decide)
def etat316 : List ℕ := [fil0,fil1,fil29,fil2,fil40]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve369 : Ban 30 4 etat316 := viaSmall (by decide +kernel) (by decide)
def etat317 : List ℕ := [fil0,fil1,fil29,fil2,fil19]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve370 : Ban 30 4 etat317 := viaSmall (by decide +kernel) (by decide)
def etat318 : List ℕ := [fil0,fil1,fil29,fil2,fil20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve371 : Ban 30 4 etat318 := viaSmall (by decide +kernel) (by decide)
def etat319 : List ℕ := [fil0,fil1,fil29,fil2,fil36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve372 : Ban 30 4 etat319 := viaSmall (by decide +kernel) (by decide)
def etat320 : List ℕ := [fil0,fil1,fil29,fil2,fil34]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve373 : Ban 30 4 etat320 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve374 : Ban 30 4 etat256 := viaSmall (by decide +kernel) (by decide)
def fil108 : ℕ := 0x39ce739fe007fff
def etat321 : List ℕ := [fil0,fil1,fil2,fil108,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve375 : Ban 30 4 etat321 := viaSmall (by decide +kernel) (by decide)
def etat322 : List ℕ := [fil0,fil29,fil2,fil35,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve376 : Ban 30 4 etat322 := viaSmall (by decide +kernel) (by decide)
def etat323 : List ℕ := [fil1,fil29,fil2,fil21,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve377 : Ban 30 4 etat323 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve363 : Ban 30 5 etat45 := viaBranch (ws := [etat39,etat17,etat18,etat311,etat23,etat20,etat312,etat174,etat36,etat313,etat314,etat315,etat316,etat317,etat318,etat319,etat320,etat256,etat31,etat47,etat321,etat50,etat322,etat323])
  (consBan preuve46 (consBan preuve26 (consBan preuve95 (consBan preuve364 (consBan preuve28 (consBan preuve97 (consBan preuve365 (consBan preuve212 (consBan preuve99 (consBan preuve366 (consBan preuve367 (consBan preuve368 (consBan preuve369 (consBan preuve370 (consBan preuve371 (consBan preuve372 (consBan preuve373 (consBan preuve374 (consBan preuve36 (consBan preuve54 (consBan preuve375 (consBan preuve57 (consBan preuve376 (consBan preuve377 (nilBan _ _)))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit13 : Wide 30 5 etat45 := viaSub (ws := [etat0,etat45])
  (consBan preuve93 (consBan preuve363 (nilBan _ _)))
  (by decide) (by decide +kernel)
def fil109 : ℕ := 0x1c71c71c71c71c7000000fffffffff
def etat324 : List ℕ := [fil43,fil44,fil65,fil45,fil109,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve378 : Ban 60 6 etat324 := viaCut proj18 petit13 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve379 : Ban 30 5 etat46 := viaPerm proj8 proj8 preuve363 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit14 : Wide 30 5 etat46 := viaSub (ws := [etat0,etat46])
  (consBan preuve93 (consBan preuve379 (nilBan _ _)))
  (by decide) (by decide +kernel)
def fil110 : ℕ := 0x1c71c71c71c71c703ffff00003ffff
def etat325 : List ℕ := [fil43,fil44,fil65,fil45,fil110,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve380 : Ban 60 6 etat325 := viaCut proj18 petit14 (by decide) (by decide +kernel) (by decide +kernel)
def fil111 : ℕ := 0x208208208208208fc0000000000000
def etat326 : List ℕ := [fil43,fil44,fil65,fil45,fil111,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve381 : Ban 60 6 etat326 := viaCut proj21 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def fil112 : ℕ := 0x3fff8000
def etat327 : List ℕ := [fil112,fil0,fil1,fil2]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve383 : Ban 30 4 etat327 := viaSmall (by decide +kernel) (by decide)
def etat328 : List ℕ := [fil112,fil0,fil1,fil2,fil32]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve384 : Ban 30 4 etat328 := viaSmall (by decide +kernel) (by decide)
def etat329 : List ℕ := [fil112,fil0,fil1,fil2,fil3]
def fil113 : ℕ := 0xf83ff
def etat330 : List ℕ := [fil113,fil0,fil1,fil2,fil3]
def etat331 : List ℕ := [fil113,fil6,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve387 : Ban 30 3 etat331 := viaSmall (by decide +kernel) (by decide)
def etat332 : List ℕ := [fil113,fil1,fil23,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve388 : Ban 30 3 etat332 := viaSmall (by decide +kernel) (by decide)
def etat333 : List ℕ := [fil113,fil1,fil2,fil19]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve389 : Ban 30 3 etat333 := viaSmall (by decide +kernel) (by decide)
def etat334 : List ℕ := [fil113,fil1,fil2,fil20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve390 : Ban 30 3 etat334 := viaSmall (by decide +kernel) (by decide)
def etat335 : List ℕ := [fil113,fil1,fil21,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve391 : Ban 30 3 etat335 := viaSmall (by decide +kernel) (by decide)
def etat336 : List ℕ := [fil113,fil9,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve392 : Ban 30 3 etat336 := viaSmall (by decide +kernel) (by decide)
def fil114 : ℕ := 0x42108423fff83ff
def etat337 : List ℕ := [fil0,fil1,fil2,fil114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve393 : Ban 30 3 etat337 := viaSmall (by decide +kernel) (by decide)
def fil115 : ℕ := 0x21084213e0fffff
def etat338 : List ℕ := [fil0,fil1,fil115,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve394 : Ban 30 3 etat338 := viaSmall (by decide +kernel) (by decide)
def fil116 : ℕ := 0x108421081ffffff
def etat339 : List ℕ := [fil0,fil116,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve395 : Ban 30 3 etat339 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve386 : Ban 30 4 etat330 := viaBranch (ws := [etat331,etat332,etat333,etat334,etat335,etat336,etat337,etat338,etat339])
  (consBan preuve387 (consBan preuve388 (consBan preuve389 (consBan preuve390 (consBan preuve391 (consBan preuve392 (consBan preuve393 (consBan preuve394 (consBan preuve395 (nilBan _ _))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve385 : Ban 30 4 etat329 := viaPerm proj12 proj11 preuve386 (by decide +kernel) (by decide +kernel)
def etat340 : List ℕ := [fil0,fil25,fil2,fil32,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve396 : Ban 30 4 etat340 := viaSmall (by decide +kernel) (by decide)
def etat341 : List ℕ := [fil0,fil1,fil30,fil32,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve397 : Ban 30 4 etat341 := viaSmall (by decide +kernel) (by decide)
def etat342 : List ℕ := [fil0,fil1,fil37,fil32,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve398 : Ban 30 4 etat342 := viaSmall (by decide +kernel) (by decide)
def fil117 : ℕ := 0x294a5297e0f83e0
def etat343 : List ℕ := [fil0,fil1,fil2,fil117,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve399 : Ban 30 4 etat343 := viaSmall (by decide +kernel) (by decide)
def fil118 : ℕ := 0x39ce739c0007fff
def etat344 : List ℕ := [fil0,fil1,fil2,fil118]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve400 : Ban 30 4 etat344 := viaSmall (by decide +kernel) (by decide)
def etat345 : List ℕ := [fil0,fil1,fil2,fil118,fil32]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve401 : Ban 30 4 etat345 := viaSmall (by decide +kernel) (by decide)
def etat346 : List ℕ := [fil0,fil1,fil2,fil118,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve402 : Ban 30 4 etat346 := viaSmall (by decide +kernel) (by decide)
def fil119 : ℕ := 0x421084200000000
def etat347 : List ℕ := [fil0,fil1,fil2,fil119,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve403 : Ban 30 4 etat347 := viaSmall (by decide +kernel) (by decide)
def fil120 : ℕ := 0x7bdef7bffffffff
def etat348 : List ℕ := [fil0,fil1,fil2,fil3,fil120]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve404 : Ban 30 4 etat348 := viaSmall (by decide +kernel) (by decide)
def etat349 : List ℕ := [fil0,fil1,fil32,fil3,fil41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve405 : Ban 30 4 etat349 := viaSmall (by decide +kernel) (by decide)
def etat350 : List ℕ := [fil0,fil2,fil117,fil32,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve406 : Ban 30 4 etat350 := viaSmall (by decide +kernel) (by decide)
def etat351 : List ℕ := [fil0,fil2,fil32,fil3,fil36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve407 : Ban 30 4 etat351 := viaSmall (by decide +kernel) (by decide)
def etat352 : List ℕ := [fil1,fil2,fil84,fil32,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve408 : Ban 30 4 etat352 := viaSmall (by decide +kernel) (by decide)
def etat353 : List ℕ := [fil1,fil2,fil32,fil3,fil20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve409 : Ban 30 4 etat353 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve382 : Ban 30 5 etat48 := viaBranch (ws := [etat327,etat328,etat329,etat207,etat340,etat46,etat341,etat342,etat343,etat212,etat344,etat345,etat346,etat347,etat348,etat349,etat350,etat351,etat352,etat353])
  (consBan preuve383 (consBan preuve384 (consBan preuve385 (consBan preuve245 (consBan preuve396 (consBan preuve53 (consBan preuve397 (consBan preuve398 (consBan preuve399 (consBan preuve250 (consBan preuve400 (consBan preuve401 (consBan preuve402 (consBan preuve403 (consBan preuve404 (consBan preuve405 (consBan preuve406 (consBan preuve407 (consBan preuve408 (consBan preuve409 (nilBan _ _)))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit15 : Wide 30 5 etat48 := viaSub (ws := [etat0,etat48])
  (consBan preuve93 (consBan preuve382 (nilBan _ _)))
  (by decide) (by decide +kernel)
def fil121 : ℕ := 0x3cf3cf3cf3cf3cffffffffffffffff
def etat354 : List ℕ := [fil43,fil44,fil65,fil45,fil46,fil121,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve410 : Ban 60 6 etat354 := viaCut proj18 petit15 (by decide) (by decide +kernel) (by decide +kernel)
def fil122 : ℕ := 0x410410410410410fc0000000000000
def etat355 : List ℕ := [fil43,fil44,fil65,fil45,fil46,fil122,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve411 : Ban 60 6 etat355 := viaCut proj22 petit6 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve412 : Ban 30 5 etat50 := viaPerm proj8 proj8 preuve382 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit16 : Wide 30 5 etat50 := viaSub (ws := [etat0,etat50])
  (consBan preuve93 (consBan preuve412 (nilBan _ _)))
  (by decide) (by decide +kernel)
def fil123 : ℕ := 0x5d75d75d75d75d7fffffffffffffff
def etat356 : List ℕ := [fil43,fil44,fil65,fil45,fil46,fil47,fil123]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve413 : Ban 60 6 etat356 := viaCut proj18 petit16 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit17 : Wide 30 4 etat239 := viaSearch (by decide +kernel)
def fil124 : ℕ := 0x4d34d34d34d34d3ffffff03fffffff
def fil125 : ℕ := 0x514514514514514fffffffc003ffc0
def etat357 : List ℕ := [fil42,fil65,fil45,fil46,fil124,fil125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve415 : Ban 60 5 etat357 := viaCut proj18 petit17 (by decide) (by decide +kernel) (by decide +kernel)
def etat358 : List ℕ := [fil87,fil0,fil1,fil2,fil20]
def etat359 : List ℕ := [fil87,fil1,fil2,fil20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve416 : Ban 30 4 etat359 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve417 : Ban 30 4 etat358 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit18 : Wide 30 4 etat358 := viaSub (ws := [etat359,etat358])
  (consBan preuve416 (consBan preuve417 (nilBan _ _)))
  (by decide) (by decide +kernel)
def fil126 : ℕ := 0xfff00003ffc0
def etat360 : List ℕ := [fil126,fil43,fil44,fil45,fil46,fil124]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve418 : Ban 60 5 etat360 := viaCut proj18 petit18 (by decide) (by decide +kernel) (by decide +kernel)
def fil127 : ℕ := 0x3f00000003ffc0
def etat361 : List ℕ := [fil127,fil43,fil44,fil65,fil46,fil125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve419 : Ban 60 5 etat361 := viaCut proj20 petit6 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit19 : Wide 30 4 etat245 := viaSearch (by decide +kernel)
def fil128 : ℕ := 0xc30c30c30c30c300000003ffc003f
def etat362 : List ℕ := [fil43,fil44,fil128,fil45,fil46,fil124]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve420 : Ban 60 5 etat362 := viaCut proj18 petit19 (by decide) (by decide +kernel) (by decide +kernel)
def fil129 : ℕ := 0x410410410410410ffffff00003ffc0
def etat363 : List ℕ := [fil43,fil44,fil65,fil45,fil46,fil129]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve421 : Ban 60 5 etat363 := viaCut proj20 petit6 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit20 : Wide 30 4 etat50 := viaSearch (by decide +kernel)
def etat364 : List ℕ := [fil43,fil44,fil97,fil46,fil124,fil125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve422 : Ban 60 5 etat364 := viaCut proj20 petit20 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit21 : Wide 30 4 etat0 := viaSearch (by decide +kernel)
def fil130 : ℕ := 0x410410410410410fff000000000000
def etat365 : List ℕ := [fil43,fil44,fil45,fil46,fil130,fil125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve423 : Ban 60 5 etat365 := viaCut proj22 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def etat366 : List ℕ := [fil0,fil9,fil2,fil20,fil36]
def etat367 : List ℕ := [fil9,fil2,fil20,fil36]
def etat368 : List ℕ := [fil0,fil35,fil36,fil41]
def fil131 : ℕ := 0x10842108000001f
def etat369 : List ℕ := [fil0,fil131,fil35,fil36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve426 : Ban 30 3 etat369 := viaSmall (by decide +kernel) (by decide)
def fil132 : ℕ := 0x1084210bff07c1f
def etat370 : List ℕ := [fil0,fil132,fil35,fil41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve427 : Ban 30 3 etat370 := viaSmall (by decide +kernel) (by decide)
def etat371 : List ℕ := [fil0,fil132,fil36,fil41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve428 : Ban 30 3 etat371 := viaSmall (by decide +kernel) (by decide)
def etat372 : List ℕ := [fil0,fil132,fil41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve429 : Ban 30 3 etat372 := viaSmall (by decide +kernel) (by decide)
def fil133 : ℕ := 0x2108421000003e0
def etat373 : List ℕ := [fil0,fil133,fil35,fil41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve430 : Ban 30 3 etat373 := viaSmall (by decide +kernel) (by decide)
def fil134 : ℕ := 0x21084213ff07fe0
def etat374 : List ℕ := [fil0,fil134,fil35,fil36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve431 : Ban 30 3 etat374 := viaSmall (by decide +kernel) (by decide)
def etat375 : List ℕ := [fil0,fil134,fil36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve432 : Ban 30 3 etat375 := viaSmall (by decide +kernel) (by decide)
def etat376 : List ℕ := [fil0,fil134,fil36,fil41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve433 : Ban 30 3 etat376 := viaSmall (by decide +kernel) (by decide)
def etat377 : List ℕ := [fil0,fil84,fil36,fil41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve434 : Ban 30 3 etat377 := viaSmall (by decide +kernel) (by decide)
def fil135 : ℕ := 0x42108423ffffc00
def etat378 : List ℕ := [fil0,fil35,fil135]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve435 : Ban 30 3 etat378 := viaSmall (by decide +kernel) (by decide)
def etat379 : List ℕ := [fil0,fil35,fil135,fil36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve436 : Ban 30 3 etat379 := viaSmall (by decide +kernel) (by decide)
def etat380 : List ℕ := [fil0,fil35,fil135,fil41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve437 : Ban 30 3 etat380 := viaSmall (by decide +kernel) (by decide)
def etat381 : List ℕ := [fil0,fil35,fil88,fil41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve438 : Ban 30 3 etat381 := viaSmall (by decide +kernel) (by decide)
def fil136 : ℕ := 0x6318c633ff07c00
def etat382 : List ℕ := [fil0,fil35,fil36,fil136]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve439 : Ban 30 3 etat382 := viaSmall (by decide +kernel) (by decide)
def fil137 : ℕ := 0x6b5ad6b7fffffff
def etat383 : List ℕ := [fil0,fil35,fil36,fil137]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve440 : Ban 30 3 etat383 := viaSmall (by decide +kernel) (by decide)
def etat384 : List ℕ := [fil0,fil35,fil34,fil41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve441 : Ban 30 3 etat384 := viaSmall (by decide +kernel) (by decide)
def etat385 : List ℕ := [fil0,fil32,fil36,fil41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve442 : Ban 30 3 etat385 := viaSmall (by decide +kernel) (by decide)
def fil138 : ℕ := 0x4210842000f8000
def etat386 : List ℕ := [fil0,fil138,fil36,fil41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve443 : Ban 30 3 etat386 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve425 : Ban 30 4 etat368 := viaBranch (ws := [etat369,etat370,etat371,etat372,etat373,etat374,etat375,etat376,etat377,etat378,etat379,etat380,etat381,etat382,etat383,etat384,etat385,etat386])
  (consBan preuve426 (consBan preuve427 (consBan preuve428 (consBan preuve429 (consBan preuve430 (consBan preuve431 (consBan preuve432 (consBan preuve433 (consBan preuve434 (consBan preuve435 (consBan preuve436 (consBan preuve437 (consBan preuve438 (consBan preuve439 (consBan preuve440 (consBan preuve441 (consBan preuve442 (consBan preuve443 (nilBan _ _)))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve424 : Ban 30 4 etat367 := viaPerm proj2 proj1 preuve425 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve444 : Ban 30 4 etat366 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit22 : Wide 30 4 etat366 := viaSub (ws := [etat367,etat366])
  (consBan preuve424 (consBan preuve444 (nilBan _ _)))
  (by decide) (by decide +kernel)
def etat387 : List ℕ := [fil43,fil44,fil102,fil46,fil124,fil125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve445 : Ban 60 5 etat387 := viaCut proj18 petit22 (by decide) (by decide +kernel) (by decide +kernel)
def etat388 : List ℕ := [fil0,fil1,fil2,fil19,fil36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit23 : Wide 30 4 etat388 := viaSearch (by decide +kernel)
def fil139 : ℕ := 0x451451451451451fff03f000fc0fc0
def etat389 : List ℕ := [fil43,fil65,fil45,fil46,fil139,fil125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve446 : Ban 60 5 etat389 := viaCut proj18 petit23 (by decide) (by decide +kernel) (by decide +kernel)
def etat390 : List ℕ := [fil43,fil65,fil101,fil46,fil124,fil125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve447 : Ban 60 5 etat390 := viaCut proj18 petit22 (by decide) (by decide +kernel) (by decide +kernel)
def fil140 : ℕ := 0x492492492492492ffffc003f03f000
def etat391 : List ℕ := [fil44,fil65,fil45,fil46,fil140,fil125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve448 : Ban 60 5 etat391 := viaCut proj19 petit23 (by decide) (by decide +kernel) (by decide +kernel)
def etat392 : List ℕ := [fil44,fil65,fil100,fil46,fil124,fil125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve449 : Ban 60 5 etat392 := viaCut proj19 petit22 (by decide) (by decide +kernel) (by decide +kernel)
def etat393 : List ℕ := [fil43,fil44,fil65,fil45,fil46,fil124,fil125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve414 : Ban 60 6 etat393 := viaBranch (ws := [etat357,etat360,etat361,etat362,etat363,etat364,etat365,etat387,etat389,etat390,etat391,etat392])
  (consBan preuve415 (consBan preuve418 (consBan preuve419 (consBan preuve420 (consBan preuve421 (consBan preuve422 (consBan preuve423 (consBan preuve445 (consBan preuve446 (consBan preuve447 (consBan preuve448 (consBan preuve449 (nilBan _ _)))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def proj23 : Projection 60 60 := pick [0,1,3,4,2,5,18,19,21,22,20,23,24,25,27,28,26,29,36,37,39,40,38,41,42,43,45,46,44,47,54,55,57,58,56,59,6,7,9,10,8,11,12,13,15,16,14,17,30,31,33,34,32,35,48,49,51,52,50,53] rfl (by decide +kernel) (by decide)
def proj24 : Projection 60 60 := pick [0,1,4,2,3,5,36,37,40,38,39,41,42,43,46,44,45,47,6,7,10,8,9,11,12,13,16,14,15,17,48,49,52,50,51,53,18,19,22,20,21,23,24,25,28,26,27,29,54,55,58,56,57,59,30,31,34,32,33,35] rfl (by decide +kernel) (by decide)
def fil141 : ℕ := 0x30c30c30c30c30cfff000fffffffc0
def etat394 : List ℕ := [fil43,fil44,fil65,fil102,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve450 : Ban 60 6 etat394 := viaPerm proj23 proj24 preuve414 (by decide +kernel) (by decide +kernel)
def proj25 : Projection 60 60 := pick [0,1,4,3,2,5,36,37,40,39,38,41,42,43,46,45,44,47,18,19,22,21,20,23,24,25,28,27,26,29,54,55,58,57,56,59,6,7,10,9,8,11,12,13,16,15,14,17,48,49,52,51,50,53,30,31,34,33,32,35] rfl (by decide +kernel) (by decide)
def etat395 : List ℕ := [fil43,fil44,fil65,fil102,fil46,fil47,fil125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve451 : Ban 60 6 etat395 := viaPerm proj25 proj25 preuve414 (by decide +kernel) (by decide +kernel)
def etat396 : List ℕ := [fil43,fil44,fil97,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve452 : Ban 60 6 etat396 := viaCut proj20 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def etat397 : List ℕ := [fil43,fil44,fil97,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve453 : Ban 60 6 etat397 := viaCut proj20 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def fil142 : ℕ := 0x208208208208208fc0000fc0000000
def etat398 : List ℕ := [fil43,fil44,fil45,fil102,fil142,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve454 : Ban 60 6 etat398 := viaCut proj21 petit7 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit24 : Wide 30 4 etat54 := viaSearch (by decide +kernel)
def fil143 : ℕ := 0x2cb2cb2cb2cb2cbfc0ffffffffffff
def etat399 : List ℕ := [fil42,fil45,fil102,fil46,fil143,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve456 : Ban 60 5 etat399 := viaCut proj18 petit24 (by decide) (by decide +kernel) (by decide +kernel)
def fil144 : ℕ := 0xfc003ffc0
def etat400 : List ℕ := [fil144,fil43,fil44,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve457 : Ban 60 5 etat400 := viaCut proj20 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def etat401 : List ℕ := [fil103,fil43,fil44,fil45,fil143,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve458 : Ban 60 5 etat401 := viaCut proj21 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def fil145 : ℕ := 0x842108400fffff
def etat402 : List ℕ := [fil0,fil145,fil1,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit25 : Wide 30 4 etat402 := viaSearch (by decide +kernel)
def fil146 : ℕ := 0xc30c30c30c30c3000ffffffffffff
def etat403 : List ℕ := [fil43,fil44,fil146,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve459 : Ban 60 5 etat403 := viaCut proj18 petit25 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit26 : Wide 30 3 etat0 := viaSearch (by decide +kernel)
def fil147 : ℕ := 0x10410410410410403f000000000000
def etat404 : List ℕ := [fil43,fil44,fil147,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve460 : Ban 60 5 etat404 := viaCut proj20 petit26 (by decide) (by decide +kernel) (by decide +kernel)
def etat405 : List ℕ := [fil0,fil1,fil30,fil21,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit27 : Wide 30 4 etat405 := viaSearch (by decide +kernel)
def etat406 : List ℕ := [fil43,fil44,fil45,fil110,fil143,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve461 : Ban 60 5 etat406 := viaCut proj18 petit27 (by decide) (by decide +kernel) (by decide +kernel)
def etat407 : List ℕ := [fil43,fil44,fil45,fil111,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve462 : Ban 60 5 etat407 := viaCut proj21 petit26 (by decide) (by decide +kernel) (by decide +kernel)
def etat408 : List ℕ := [fil43,fil44,fil45,fil46,fil121,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve463 : Ban 60 5 etat408 := viaCut proj18 petit7 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit28 : Wide 30 4 etat341 := viaSearch (by decide +kernel)
def fil148 : ℕ := 0x2cb2cb2cb2cb2cbfc0fff03ffc003f
def etat409 : List ℕ := [fil43,fil44,fil102,fil46,fil148,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve464 : Ban 60 5 etat409 := viaCut proj21 petit28 (by decide) (by decide +kernel) (by decide +kernel)
def etat410 : List ℕ := [fil0,fil9,fil21,fil35,fil3]
def etat411 : List ℕ := [fil9,fil21,fil35,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve465 : Ban 30 4 etat411 := viaPerm proj12 proj11 preuve425 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve466 : Ban 30 4 etat410 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit29 : Wide 30 4 etat410 := viaSub (ws := [etat411,etat410])
  (consBan preuve465 (consBan preuve466 (nilBan _ _)))
  (by decide) (by decide +kernel)
def etat412 : List ℕ := [fil43,fil44,fil102,fil143,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve467 : Ban 60 5 etat412 := viaCut proj18 petit29 (by decide) (by decide +kernel) (by decide +kernel)
def etat413 : List ℕ := [fil43,fil44,fil45,fil102,fil46,fil143,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve455 : Ban 60 6 etat413 := viaBranch (ws := [etat399,etat400,etat401,etat403,etat404,etat406,etat407,etat408,etat409,etat412])
  (consBan preuve456 (consBan preuve457 (consBan preuve458 (consBan preuve459 (consBan preuve460 (consBan preuve461 (consBan preuve462 (consBan preuve463 (consBan preuve464 (consBan preuve467 (nilBan _ _)))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def etat414 : List ℕ := [fil43,fil44,fil45,fil102,fil46,fil130,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve468 : Ban 60 6 etat414 := viaCut proj22 petit7 (by decide) (by decide +kernel) (by decide +kernel)
def proj26 : Projection 60 60 := pick [0,1,2,4,3,5,6,7,8,10,9,11,12,13,14,16,15,17,36,37,38,40,39,41,42,43,44,46,45,47,48,49,50,52,51,53,18,19,20,22,21,23,24,25,26,28,27,29,30,31,32,34,33,35,54,55,56,58,57,59] rfl (by decide +kernel) (by decide)
def etat415 : List ℕ := [fil43,fil44,fil45,fil102,fil46,fil47,fil124]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve469 : Ban 60 6 etat415 := viaPerm proj26 proj26 preuve455 (by decide +kernel) (by decide +kernel)
def etat416 : List ℕ := [fil43,fil65,fil45,fil105,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve470 : Ban 60 6 etat416 := viaCut proj20 petit11 (by decide) (by decide +kernel) (by decide +kernel)
def etat417 : List ℕ := [fil43,fil65,fil45,fil105,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve471 : Ban 60 6 etat417 := viaCut proj18 petit12 (by decide) (by decide +kernel) (by decide +kernel)
def etat418 : List ℕ := [fil43,fil65,fil45,fil101,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve472 : Ban 60 6 etat418 := viaCut proj18 petit2 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit30 : Wide 30 4 etat63 := viaSearch (by decide +kernel)
def fil149 : ℕ := 0x3f00000003f
def fil150 : ℕ := 0x451451451451451ffffff000fc0fff
def fil151 : ℕ := 0x555555555555555fffffffc0ffffff
def etat419 : List ℕ := [fil149,fil44,fil45,fil46,fil150,fil151]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve474 : Ban 60 5 etat419 := viaCut proj18 petit30 (by decide) (by decide +kernel) (by decide +kernel)
def fil152 : ℕ := 0xfc000000003f
def fil153 : ℕ := 0x492492492492492ffffff03f03f03f
def etat420 : List ℕ := [fil152,fil43,fil45,fil46,fil153,fil151]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve475 : Ban 60 5 etat420 := viaCut proj19 petit20 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit31 : Wide 30 4 etat34 := viaSearch (by decide +kernel)
def fil154 : ℕ := 0xfc000003f03f
def etat421 : List ℕ := [fil154,fil43,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve476 : Ban 60 5 etat421 := viaCut proj19 petit31 (by decide) (by decide +kernel) (by decide +kernel)
def fil155 : ℕ := 0x3f000000000fc0
def etat422 : List ℕ := [fil155,fil43,fil44,fil46,fil153,fil151]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve477 : Ban 60 5 etat422 := viaCut proj20 petit17 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit32 : Wide 30 4 etat174 := viaSearch (by decide +kernel)
def fil156 : ℕ := 0x145145145145145000000fc0fc0fc0
def etat423 : List ℕ := [fil43,fil44,fil45,fil156,fil46,fil150]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve478 : Ban 60 5 etat423 := viaCut proj18 petit32 (by decide) (by decide +kernel) (by decide +kernel)
def fil157 : ℕ := 0x410410410410410ffffff00000003f
def etat424 : List ℕ := [fil43,fil44,fil45,fil46,fil157,fil151]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve479 : Ban 60 5 etat424 := viaCut proj18 petit30 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit33 : Wide 30 4 etat12 := viaSearch (by decide +kernel)
def fil158 : ℕ := 0x410410410410410ffffff00003f03f
def etat425 : List ℕ := [fil43,fil44,fil45,fil46,fil158,fil150]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve480 : Ban 60 5 etat425 := viaCut proj18 petit33 (by decide) (by decide +kernel) (by decide +kernel)
def fil159 : ℕ := 0x4a5294a7e0f83e0
def etat426 : List ℕ := [fil0,fil2,fil3,fil159,fil34]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit34 : Wide 30 4 etat426 := viaSearch (by decide +kernel)
def fil160 : ℕ := 0x451451451451451fc0fff000fc003f
def etat427 : List ℕ := [fil43,fil44,fil46,fil160,fil153,fil151]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve481 : Ban 60 5 etat427 := viaCut proj19 petit34 (by decide) (by decide +kernel) (by decide +kernel)
def etat428 : List ℕ := [fil0,fil2,fil159,fil20,fil36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit35 : Wide 30 4 etat428 := viaSearch (by decide +kernel)
def etat429 : List ℕ := [fil43,fil45,fil46,fil139,fil153,fil151]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve482 : Ban 60 5 etat429 := viaCut proj20 petit35 (by decide) (by decide +kernel) (by decide +kernel)
def etat430 : List ℕ := [fil1,fil2,fil3,fil20,fil88]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit36 : Wide 30 4 etat430 := viaSearch (by decide +kernel)
def fil161 : ℕ := 0x555555555555555fff03ffc0fc0fc0
def etat431 : List ℕ := [fil43,fil45,fil46,fil150,fil153,fil161]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve483 : Ban 60 5 etat431 := viaCut proj18 petit36 (by decide) (by decide +kernel) (by decide +kernel)
def etat432 : List ℕ := [fil9,fil2,fil3,fil20,fil36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve484 : Ban 30 4 etat432 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit37 : Wide 30 4 etat432 := viaSub (ws := [etat367,etat432])
  (consBan preuve424 (consBan preuve484 (nilBan _ _)))
  (by decide) (by decide +kernel)
def etat433 : List ℕ := [fil43,fil101,fil46,fil150,fil153,fil151]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve485 : Ban 60 5 etat433 := viaCut proj18 petit37 (by decide) (by decide +kernel) (by decide +kernel)
def fil162 : ℕ := 0x514514514514514ffffc0fc003f000
def etat434 : List ℕ := [fil44,fil45,fil46,fil150,fil153,fil162]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve486 : Ban 60 5 etat434 := viaCut proj19 petit36 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit38 : Wide 30 4 etat367 := viaSub (ws := [etat367])
  (consBan preuve424 (nilBan _ _))
  (by decide) (by decide +kernel)
def etat435 : List ℕ := [fil65,fil45,fil46,fil150,fil153,fil151]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve487 : Ban 60 5 etat435 := viaCut proj20 petit38 (by decide) (by decide +kernel) (by decide +kernel)
def etat436 : List ℕ := [fil43,fil44,fil45,fil46,fil150,fil153,fil151]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve473 : Ban 60 6 etat436 := viaBranch (ws := [etat419,etat420,etat421,etat422,etat423,etat424,etat425,etat427,etat429,etat431,etat433,etat434,etat435])
  (consBan preuve474 (consBan preuve475 (consBan preuve476 (consBan preuve477 (consBan preuve478 (consBan preuve479 (consBan preuve480 (consBan preuve481 (consBan preuve482 (consBan preuve483 (consBan preuve485 (consBan preuve486 (consBan preuve487 (nilBan _ _))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def proj27 : Projection 60 60 := pick [18,21,20,22,19,23,6,9,8,10,7,11,30,33,32,34,31,35,36,39,38,40,37,41,54,57,56,58,55,59,48,51,50,52,49,53,0,3,2,4,1,5,24,27,26,28,25,29,12,15,14,16,13,17,42,45,44,46,43,47] rfl (by decide +kernel) (by decide)
def proj28 : Projection 60 60 := pick [36,40,38,37,39,41,6,10,8,7,9,11,48,52,50,49,51,53,0,4,2,1,3,5,42,46,44,43,45,47,12,16,14,13,15,17,18,22,20,19,21,23,54,58,56,55,57,59,30,34,32,31,33,35,24,28,26,25,27,29] rfl (by decide +kernel) (by decide)
def fil163 : ℕ := 0x28a28a28a28a28afc0fc0ffffff03f
def etat437 : List ℕ := [fil43,fil65,fil45,fil102,fil46,fil163,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve488 : Ban 60 6 etat437 := viaPerm proj27 proj28 preuve473 (by decide +kernel) (by decide +kernel)
def proj29 : Projection 60 60 := pick [36,40,38,39,37,41,6,10,8,9,7,11,48,52,50,51,49,53,18,22,20,21,19,23,54,58,56,57,55,59,30,34,32,33,31,35,0,4,2,3,1,5,42,46,44,45,43,47,12,16,14,15,13,17,24,28,26,27,25,29] rfl (by decide +kernel) (by decide)
def etat438 : List ℕ := [fil43,fil65,fil45,fil102,fil46,fil47,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve489 : Ban 60 6 etat438 := viaPerm proj29 proj29 preuve473 (by decide +kernel) (by decide +kernel)
def etat439 : List ℕ := [fil64,fil44,fil65,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve490 : Ban 60 6 etat439 := viaCut proj19 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def etat440 : List ℕ := [fil44,fil65,fil45,fil100,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve491 : Ban 60 6 etat440 := viaCut proj19 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat441 : List ℕ := [fil0,fil6,fil1,fil9,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve492 : Ban 30 5 etat53 := viaPerm proj11 proj12 preuve281 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve493 : Ban 30 5 etat441 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit39 : Wide 30 5 etat441 := viaSub (ws := [etat0,etat10,etat38,etat53,etat441])
  (consBan preuve93 (consBan preuve44 (consBan preuve45 (consBan preuve492 (consBan preuve493 (nilBan _ _))))))
  (by decide) (by decide +kernel)
def etat442 : List ℕ := [fil44,fil65,fil45,fil106,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve494 : Ban 60 6 etat442 := viaCut proj19 petit39 (by decide) (by decide +kernel) (by decide +kernel)
def etat443 : List ℕ := [fil44,fil65,fil45,fil106,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve495 : Ban 60 6 etat443 := viaCut proj19 petit12 (by decide) (by decide +kernel) (by decide +kernel)
def proj30 : Projection 60 60 := pick [25,27,26,28,24,29,13,15,14,16,12,17,31,33,32,34,30,35,43,45,44,46,42,47,55,57,56,58,54,59,49,51,50,52,48,53,1,3,2,4,0,5,19,21,20,22,18,23,7,9,8,10,6,11,37,39,38,40,36,41] rfl (by decide +kernel) (by decide)
def proj31 : Projection 60 60 := pick [40,36,38,37,39,41,52,48,50,49,51,53,10,6,8,7,9,11,46,42,44,43,45,47,4,0,2,1,3,5,16,12,14,13,15,17,58,54,56,55,57,59,22,18,20,19,21,23,34,30,32,31,33,35,28,24,26,25,27,29] rfl (by decide +kernel) (by decide)
def fil164 : ℕ := 0x249249249249249fc003fffffc0fff
def etat444 : List ℕ := [fil44,fil65,fil45,fil102,fil46,fil164,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve496 : Ban 60 6 etat444 := viaPerm proj30 proj31 preuve473 (by decide +kernel) (by decide +kernel)
def proj32 : Projection 60 60 := pick [43,46,44,45,42,47,13,16,14,15,12,17,49,52,50,51,48,53,25,28,26,27,24,29,55,58,56,57,54,59,31,34,32,33,30,35,1,4,2,3,0,5,37,40,38,39,36,41,7,10,8,9,6,11,19,22,20,21,18,23] rfl (by decide +kernel) (by decide)
def proj33 : Projection 60 60 := pick [40,36,38,39,37,41,52,48,50,51,49,53,10,6,8,9,7,11,58,54,56,57,55,59,22,18,20,21,19,23,34,30,32,33,31,35,46,42,44,45,43,47,4,0,2,3,1,5,16,12,14,15,13,17,28,24,26,27,25,29] rfl (by decide +kernel) (by decide)
def etat445 : List ℕ := [fil44,fil65,fil45,fil102,fil46,fil47,fil150]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve497 : Ban 60 6 etat445 := viaPerm proj32 proj33 preuve473 (by decide +kernel) (by decide +kernel)
def etat446 : List ℕ := [fil43,fil44,fil65,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve329 : Ban 60 7 etat446 := viaBranch (ws := [etat282,etat283,etat284,etat285,etat286,etat287,etat288,etat289,etat290,etat291,etat292,etat293,etat294,etat295,etat296,etat297,etat298,etat299,etat300,etat301,etat303,etat273,etat304,etat305,etat306,etat307,etat308,etat277,etat309,etat310,etat324,etat325,etat326,etat354,etat355,etat356,etat394,etat395,etat396,etat397,etat398,etat413,etat414,etat415,etat416,etat417,etat418,etat437,etat438,etat439,etat440,etat442,etat443,etat444,etat445])
  (consBan preuve330 (consBan preuve331 (consBan preuve332 (consBan preuve333 (consBan preuve334 (consBan preuve335 (consBan preuve336 (consBan preuve337 (consBan preuve338 (consBan preuve339 (consBan preuve340 (consBan preuve341 (consBan preuve342 (consBan preuve343 (consBan preuve344 (consBan preuve345 (consBan preuve346 (consBan preuve347 (consBan preuve348 (consBan preuve349 (consBan preuve352 (consBan preuve353 (consBan preuve355 (consBan preuve356 (consBan preuve357 (consBan preuve358 (consBan preuve359 (consBan preuve360 (consBan preuve361 (consBan preuve362 (consBan preuve378 (consBan preuve380 (consBan preuve381 (consBan preuve410 (consBan preuve411 (consBan preuve413 (consBan preuve450 (consBan preuve451 (consBan preuve452 (consBan preuve453 (consBan preuve454 (consBan preuve455 (consBan preuve468 (consBan preuve469 (consBan preuve470 (consBan preuve471 (consBan preuve472 (consBan preuve488 (consBan preuve489 (consBan preuve490 (consBan preuve491 (consBan preuve494 (consBan preuve495 (consBan preuve496 (consBan preuve497 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def fil165 : ℕ := 0x208208208208208000000ffffc0000
def etat447 : List ℕ := [fil43,fil44,fil65,fil45,fil165,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve498 : Ban 60 7 etat447 := viaCut proj21 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def fil166 : ℕ := 0x208208208208208fc000003ffc0000
def etat448 : List ℕ := [fil43,fil44,fil65,fil45,fil166,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve499 : Ban 60 7 etat448 := viaCut proj21 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat449 : List ℕ := [fil43,fil44,fil65,fil45,fil142,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve500 : Ban 60 7 etat449 := viaCut proj21 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def fil167 : ℕ := 0x208208208208208fc0000fc0fc0000
def etat450 : List ℕ := [fil43,fil44,fil65,fil45,fil167,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve501 : Ban 60 7 etat450 := viaCut proj21 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def fil168 : ℕ := 0x208208208208208fc0000fff000000
def etat451 : List ℕ := [fil43,fil44,fil65,fil45,fil168,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve502 : Ban 60 7 etat451 := viaCut proj21 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat452 : List ℕ := [fil43,fil44,fil65,fil45,fil46,fil164,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve503 : Ban 60 7 etat452 := viaCut proj18 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def etat453 : List ℕ := [fil43,fil44,fil65,fil45,fil46,fil163,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve504 : Ban 60 7 etat453 := viaCut proj19 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def proj34 : Projection 60 60 := pick [0,1,3,2,4,5,18,19,21,20,22,23,24,25,27,26,28,29,6,7,9,8,10,11,12,13,15,14,16,17,30,31,33,32,34,35,36,37,39,38,40,41,42,43,45,44,46,47,54,55,57,56,58,59,48,49,51,50,52,53] rfl (by decide +kernel) (by decide)
def etat454 : List ℕ := [fil43,fil44,fil65,fil45,fil46,fil143,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve505 : Ban 60 7 etat454 := viaPerm proj34 proj34 preuve329 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit40 : Wide 30 4 etat59 := viaSearch (by decide +kernel)
def etat455 : List ℕ := [fil42,fil43,fil65,fil45,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve507 : Ban 60 6 etat455 := viaCut proj18 petit40 (by decide) (by decide +kernel) (by decide +kernel)
def etat456 : List ℕ := [fil42,fil44,fil65,fil45,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve508 : Ban 60 6 etat456 := viaCut proj19 petit40 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit41 : Wide 30 5 etat59 := viaSub (ws := [etat0,etat59])
  (consBan preuve93 (consBan preuve67 (nilBan _ _)))
  (by decide) (by decide +kernel)
def etat457 : List ℕ := [fil42,fil65,fil45,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve509 : Ban 60 6 etat457 := viaCut proj18 petit41 (by decide) (by decide +kernel) (by decide +kernel)
def etat458 : List ℕ := [fil66,fil43,fil44,fil45,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve510 : Ban 60 6 etat458 := viaCut proj20 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def fil169 : ℕ := 0xfc0fc0
def etat459 : List ℕ := [fil169,fil43,fil44,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve511 : Ban 60 6 etat459 := viaCut proj18 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def fil170 : ℕ := 0x3f03f000
def etat460 : List ℕ := [fil170,fil43,fil44,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve512 : Ban 60 6 etat460 := viaCut proj19 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def etat461 : List ℕ := [fil67,fil43,fil44,fil45,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve513 : Ban 60 6 etat461 := viaCut proj21 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def etat462 : List ℕ := [fil81,fil12,fil1,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve515 : Ban 30 4 etat462 := viaSmall (by decide +kernel) (by decide)
def etat463 : List ℕ := [fil81,fil73,fil1,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve516 : Ban 30 4 etat463 := viaSmall (by decide +kernel) (by decide)
def etat464 : List ℕ := [fil81,fil18,fil1,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve517 : Ban 30 4 etat464 := viaSmall (by decide +kernel) (by decide)
def etat465 : List ℕ := [fil81,fil5,fil1,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve518 : Ban 30 4 etat465 := viaSmall (by decide +kernel) (by decide)
def etat466 : List ℕ := [fil81,fil0,fil6,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve519 : Ban 30 4 etat466 := viaSmall (by decide +kernel) (by decide)
def etat467 : List ℕ := [fil81,fil0,fil1,fil23,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve520 : Ban 30 4 etat467 := viaSmall (by decide +kernel) (by decide)
def etat468 : List ℕ := [fil81,fil0,fil1,fil2,fil114]
def etat469 : List ℕ := [fil81,fil1,fil21,fil114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve522 : Ban 30 3 etat469 := viaSmall (by decide +kernel) (by decide)
def etat470 : List ℕ := [fil81,fil9,fil2,fil114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve523 : Ban 30 3 etat470 := viaSmall (by decide +kernel) (by decide)
def etat471 : List ℕ := [fil73,fil1,fil2,fil114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve524 : Ban 30 3 etat471 := viaSmall (by decide +kernel) (by decide)
def etat472 : List ℕ := [fil0,fil6,fil2,fil114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve525 : Ban 30 3 etat472 := viaSmall (by decide +kernel) (by decide)
def etat473 : List ℕ := [fil0,fil1,fil23,fil114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve526 : Ban 30 3 etat473 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve527 : Ban 30 3 etat0 := viaSmall (by decide +kernel) (by decide)
def etat474 : List ℕ := [fil0,fil1,fil8,fil114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve528 : Ban 30 3 etat474 := viaSmall (by decide +kernel) (by decide)
def fil171 : ℕ := 0x108421081f07fff
def etat475 : List ℕ := [fil0,fil171,fil2,fil114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve529 : Ban 30 3 etat475 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve521 : Ban 30 4 etat468 := viaBranch (ws := [etat469,etat470,etat471,etat472,etat473,etat0,etat474,etat475])
  (consBan preuve522 (consBan preuve523 (consBan preuve524 (consBan preuve525 (consBan preuve526 (consBan preuve527 (consBan preuve528 (consBan preuve529 (nilBan _ _)))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def etat476 : List ℕ := [fil81,fil0,fil1,fil8,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve530 : Ban 30 4 etat476 := viaSmall (by decide +kernel) (by decide)
def etat477 : List ℕ := [fil81,fil0,fil1,fil21,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve531 : Ban 30 4 etat477 := viaSmall (by decide +kernel) (by decide)
def etat478 : List ℕ := [fil81,fil0,fil171,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve532 : Ban 30 4 etat478 := viaSmall (by decide +kernel) (by decide)
def etat479 : List ℕ := [fil81,fil0,fil9,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve533 : Ban 30 4 etat479 := viaSmall (by decide +kernel) (by decide)
def etat480 : List ℕ := [fil81,fil1,fil9,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve534 : Ban 30 4 etat480 := viaSmall (by decide +kernel) (by decide)
def etat481 : List ℕ := [fil81,fil1,fil2,fil21,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve535 : Ban 30 4 etat481 := viaSmall (by decide +kernel) (by decide)
def etat482 : List ℕ := [fil81,fil1,fil2,fil19,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve536 : Ban 30 4 etat482 := viaSmall (by decide +kernel) (by decide)
def etat483 : List ℕ := [fil81,fil1,fil21,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve537 : Ban 30 4 etat483 := viaSmall (by decide +kernel) (by decide)
def etat484 : List ℕ := [fil81,fil9,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve538 : Ban 30 4 etat484 := viaSmall (by decide +kernel) (by decide)
def etat485 : List ℕ := [fil73,fil0,fil1,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve539 : Ban 30 4 etat485 := viaSmall (by decide +kernel) (by decide)
def etat486 : List ℕ := [fil0,fil1,fil171,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve540 : Ban 30 4 etat486 := viaSmall (by decide +kernel) (by decide)
def etat487 : List ℕ := [fil0,fil1,fil2,fil3,fil114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve541 : Ban 30 4 etat487 := viaSmall (by decide +kernel) (by decide)
def etat488 : List ℕ := [fil113,fil1,fil2,fil114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve543 : Ban 30 3 etat488 := viaSmall (by decide +kernel) (by decide)
def etat489 : List ℕ := [fil18,fil1,fil2,fil114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve544 : Ban 30 3 etat489 := viaSmall (by decide +kernel) (by decide)
def etat490 : List ℕ := [fil5,fil1,fil2,fil114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve545 : Ban 30 3 etat490 := viaSmall (by decide +kernel) (by decide)
def etat491 : List ℕ := [fil0,fil1,fil21,fil114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve546 : Ban 30 3 etat491 := viaSmall (by decide +kernel) (by decide)
def etat492 : List ℕ := [fil0,fil9,fil2,fil114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve547 : Ban 30 3 etat492 := viaSmall (by decide +kernel) (by decide)
def etat493 : List ℕ := [fil1,fil9,fil2,fil114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve548 : Ban 30 3 etat493 := viaSmall (by decide +kernel) (by decide)
def etat494 : List ℕ := [fil1,fil2,fil21,fil114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve549 : Ban 30 3 etat494 := viaSmall (by decide +kernel) (by decide)
def etat495 : List ℕ := [fil1,fil2,fil19,fil114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve550 : Ban 30 3 etat495 := viaSmall (by decide +kernel) (by decide)
def etat496 : List ℕ := [fil1,fil21,fil114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve551 : Ban 30 3 etat496 := viaSmall (by decide +kernel) (by decide)
def etat497 : List ℕ := [fil9,fil2,fil114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve552 : Ban 30 3 etat497 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve542 : Ban 30 4 etat337 := viaBranch (ws := [etat488,etat489,etat490,etat472,etat473,etat491,etat492,etat493,etat494,etat495,etat496,etat497])
  (consBan preuve543 (consBan preuve544 (consBan preuve545 (consBan preuve525 (consBan preuve526 (consBan preuve546 (consBan preuve547 (consBan preuve548 (consBan preuve549 (consBan preuve550 (consBan preuve551 (consBan preuve552 (nilBan _ _)))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def etat498 : List ℕ := [fil0,fil171,fil2,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve553 : Ban 30 4 etat498 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve514 : Ban 30 5 etat203 := viaBranch (ws := [etat1,etat15,etat462,etat463,etat464,etat465,etat466,etat467,etat468,etat476,etat477,etat478,etat479,etat480,etat481,etat482,etat483,etat484,etat485,etat10,etat486,etat32,etat11,etat487,etat337,etat14,etat498])
  (consBan preuve23 (consBan preuve24 (consBan preuve515 (consBan preuve516 (consBan preuve517 (consBan preuve518 (consBan preuve519 (consBan preuve520 (consBan preuve521 (consBan preuve530 (consBan preuve531 (consBan preuve532 (consBan preuve533 (consBan preuve534 (consBan preuve535 (consBan preuve536 (consBan preuve537 (consBan preuve538 (consBan preuve539 (consBan preuve12 (consBan preuve540 (consBan preuve37 (consBan preuve13 (consBan preuve541 (consBan preuve542 (consBan preuve16 (consBan preuve553 (nilBan _ _))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit42 : Wide 30 5 etat203 := viaSub (ws := [etat0,etat203])
  (consBan preuve93 (consBan preuve514 (nilBan _ _)))
  (by decide) (by decide +kernel)
def fil172 : ℕ := 0x3fffffc0
def etat499 : List ℕ := [fil172,fil43,fil44,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve554 : Ban 60 6 etat499 := viaCut proj18 petit42 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve555 : Ban 30 5 etat39 := viaPerm proj2 proj1 preuve514 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit43 : Wide 30 5 etat39 := viaSub (ws := [etat0,etat39])
  (consBan preuve93 (consBan preuve555 (nilBan _ _)))
  (by decide) (by decide +kernel)
def etat500 : List ℕ := [fil172,fil43,fil44,fil45,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve556 : Ban 60 6 etat500 := viaCut proj20 petit43 (by decide) (by decide +kernel) (by decide +kernel)
def etat501 : List ℕ := [fil172,fil43,fil44,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve557 : Ban 60 6 etat501 := viaCut proj18 petit42 (by decide) (by decide +kernel) (by decide +kernel)
def etat502 : List ℕ := [fil52,fil43,fil44,fil65,fil45,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve558 : Ban 60 6 etat502 := viaCut proj20 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def etat503 : List ℕ := [fil52,fil43,fil44,fil65,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve559 : Ban 60 6 etat503 := viaCut proj21 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def etat504 : List ℕ := [fil52,fil43,fil44,fil65,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve560 : Ban 60 6 etat504 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit44 : Wide 30 4 etat64 := viaSearch (by decide +kernel)
def etat505 : List ℕ := [fil68,fil43,fil44,fil45,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve561 : Ban 60 6 etat505 := viaCut proj22 petit44 (by decide) (by decide +kernel) (by decide +kernel)
def fil173 : ℕ := 0xfff000000000000
def etat506 : List ℕ := [fil173,fil43,fil44,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve562 : Ban 60 6 etat506 := viaCut proj22 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def etat507 : List ℕ := [fil57,fil44,fil65,fil45,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve563 : Ban 60 6 etat507 := viaCut proj18 petit41 (by decide) (by decide +kernel) (by decide +kernel)
def fil174 : ℕ := 0x4104104104104100003f00000003f
def etat508 : List ℕ := [fil174,fil43,fil44,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve564 : Ban 60 6 etat508 := viaCut proj18 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def etat509 : List ℕ := [fil174,fil44,fil65,fil45,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve565 : Ban 60 6 etat509 := viaCut proj18 petit41 (by decide) (by decide +kernel) (by decide +kernel)
def etat510 : List ℕ := [fil174,fil44,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve566 : Ban 60 6 etat510 := viaCut proj18 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat511 : List ℕ := [fil58,fil44,fil65,fil45,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve567 : Ban 60 6 etat511 := viaCut proj21 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat512 : List ℕ := [fil59,fil44,fil65,fil45,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve568 : Ban 60 6 etat512 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat513 : List ℕ := [fil60,fil43,fil44,fil45,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve569 : Ban 60 6 etat513 := viaCut proj18 petit40 (by decide) (by decide +kernel) (by decide +kernel)
def etat514 : List ℕ := [fil60,fil43,fil65,fil45,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve570 : Ban 60 6 etat514 := viaCut proj18 petit40 (by decide) (by decide +kernel) (by decide +kernel)
def etat515 : List ℕ := [fil43,fil61,fil65,fil45,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve571 : Ban 60 6 etat515 := viaCut proj19 petit41 (by decide) (by decide +kernel) (by decide +kernel)
def fil175 : ℕ := 0x82082082082082000fc000000003f
def etat516 : List ℕ := [fil43,fil175,fil44,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve572 : Ban 60 6 etat516 := viaCut proj19 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def etat517 : List ℕ := [fil43,fil175,fil65,fil45,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve573 : Ban 60 6 etat517 := viaCut proj19 petit41 (by decide) (by decide +kernel) (by decide +kernel)
def etat518 : List ℕ := [fil43,fil175,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve574 : Ban 60 6 etat518 := viaCut proj19 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat519 : List ℕ := [fil43,fil62,fil65,fil45,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve575 : Ban 60 6 etat519 := viaCut proj21 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat520 : List ℕ := [fil43,fil63,fil65,fil45,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve576 : Ban 60 6 etat520 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat521 : List ℕ := [fil43,fil64,fil44,fil45,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve577 : Ban 60 6 etat521 := viaCut proj19 petit40 (by decide) (by decide +kernel) (by decide +kernel)
def etat522 : List ℕ := [fil43,fil44,fil92,fil45,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve578 : Ban 60 6 etat522 := viaCut proj20 petit13 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve579 : Ban 30 5 etat485 := viaPerm proj3 proj4 preuve177 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit45 : Wide 30 5 etat485 := viaSub (ws := [etat0,etat485])
  (consBan preuve93 (consBan preuve579 (nilBan _ _)))
  (by decide) (by decide +kernel)
def fil176 : ℕ := 0xc30c30c30c30c3000fff00000003f
def etat523 : List ℕ := [fil43,fil44,fil176,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve580 : Ban 60 6 etat523 := viaCut proj18 petit45 (by decide) (by decide +kernel) (by decide +kernel)
def etat524 : List ℕ := [fil43,fil44,fil176,fil45,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve581 : Ban 60 6 etat524 := viaCut proj20 petit14 (by decide) (by decide +kernel) (by decide +kernel)
def etat525 : List ℕ := [fil43,fil44,fil176,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve582 : Ban 60 6 etat525 := viaCut proj18 petit45 (by decide) (by decide +kernel) (by decide +kernel)
def etat526 : List ℕ := [fil43,fil44,fil93,fil45,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve583 : Ban 60 6 etat526 := viaCut proj20 petit14 (by decide) (by decide +kernel) (by decide +kernel)
def etat527 : List ℕ := [fil43,fil44,fil94,fil45,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve584 : Ban 60 6 etat527 := viaCut proj21 petit14 (by decide) (by decide +kernel) (by decide +kernel)
def etat528 : List ℕ := [fil43,fil44,fil65,fil95,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve585 : Ban 60 6 etat528 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve586 : Ban 60 6 etat276 := viaCut proj20 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def etat529 : List ℕ := [fil43,fil44,fil65,fil96,fil45,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve587 : Ban 60 6 etat529 := viaCut proj20 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def etat530 : List ℕ := [fil43,fil44,fil65,fil97,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve588 : Ban 60 6 etat530 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat531 : List ℕ := [fil43,fil44,fil65,fil98,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve589 : Ban 60 6 etat531 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat532 : List ℕ := [fil43,fil44,fil65,fil99,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve590 : Ban 60 6 etat532 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat533 : List ℕ := [fil43,fil44,fil65,fil45,fil165,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve591 : Ban 60 6 etat533 := viaCut proj21 petit2 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve592 : Ban 60 6 etat448 := viaCut proj21 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def etat534 : List ℕ := [fil43,fil44,fil65,fil45,fil142,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve593 : Ban 60 6 etat534 := viaCut proj21 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat535 : List ℕ := [fil43,fil44,fil65,fil45,fil167,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve594 : Ban 60 6 etat535 := viaCut proj21 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat536 : List ℕ := [fil43,fil44,fil65,fil45,fil168,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve595 : Ban 60 6 etat536 := viaCut proj21 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat537 : List ℕ := [fil0,fil1,fil2,fil83,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve596 : Ban 30 5 etat537 := viaPerm proj1 proj2 preuve363 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit46 : Wide 30 5 etat537 := viaSub (ws := [etat0,etat537])
  (consBan preuve93 (consBan preuve596 (nilBan _ _)))
  (by decide) (by decide +kernel)
def fil177 : ℕ := 0x30c30c30c30c30c000000fffffffc0
def etat538 : List ℕ := [fil43,fil44,fil65,fil45,fil46,fil177,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve597 : Ban 60 6 etat538 := viaCut proj18 petit46 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve598 : Ban 30 5 etat212 := viaPerm proj11 proj12 preuve363 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit47 : Wide 30 5 etat212 := viaSub (ws := [etat0,etat212])
  (consBan preuve93 (consBan preuve598 (nilBan _ _)))
  (by decide) (by decide +kernel)
def fil178 : ℕ := 0x30c30c30c30c30cfff000fc0000000
def etat539 : List ℕ := [fil43,fil44,fil65,fil45,fil46,fil178,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve599 : Ban 60 6 etat539 := viaCut proj18 petit47 (by decide) (by decide +kernel) (by decide +kernel)
def fil179 : ℕ := 0x30c30c30c30c30cfff000fc0fc0fc0
def etat540 : List ℕ := [fil43,fil44,fil65,fil45,fil46,fil179,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve600 : Ban 60 6 etat540 := viaCut proj18 petit47 (by decide) (by decide +kernel) (by decide +kernel)
def fil180 : ℕ := 0x30c30c30c30c30cfff000fff03f000
def etat541 : List ℕ := [fil43,fil44,fil65,fil45,fil46,fil180,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve601 : Ban 60 6 etat541 := viaCut proj19 petit47 (by decide) (by decide +kernel) (by decide +kernel)
def fil181 : ℕ := 0x34d34d34d34d34dfff03ffffffffff
def etat542 : List ℕ := [fil43,fil44,fil65,fil45,fil46,fil181,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve602 : Ban 60 6 etat542 := viaCut proj18 petit41 (by decide) (by decide +kernel) (by decide +kernel)
def fil182 : ℕ := 0x38e38e38e38e38effffc0fffffffff
def etat543 : List ℕ := [fil43,fil44,fil65,fil45,fil46,fil182,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve603 : Ban 60 6 etat543 := viaCut proj19 petit41 (by decide) (by decide +kernel) (by decide +kernel)
def fil183 : ℕ := 0x410410410410410000fff000000000
def etat544 : List ℕ := [fil43,fil44,fil65,fil45,fil46,fil183,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve604 : Ban 60 6 etat544 := viaCut proj22 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def fil184 : ℕ := 0x739ce73bfffffff
def etat545 : List ℕ := [fil0,fil1,fil2,fil3,fil184]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve605 : Ban 30 5 etat545 := viaPerm proj11 proj12 preuve382 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit48 : Wide 30 5 etat545 := viaSub (ws := [etat0,etat545])
  (consBan preuve93 (consBan preuve605 (nilBan _ _)))
  (by decide) (by decide +kernel)
def fil185 : ℕ := 0x71c71c71c71c71cfffffffffffffc0
def etat546 : List ℕ := [fil43,fil44,fil65,fil45,fil46,fil47,fil185]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve606 : Ban 60 6 etat546 := viaCut proj18 petit48 (by decide) (by decide +kernel) (by decide +kernel)
def etat547 : List ℕ := [fil43,fil44,fil65,fil45,fil164,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve607 : Ban 60 6 etat547 := viaCut proj18 petit41 (by decide) (by decide +kernel) (by decide +kernel)
def etat548 : List ℕ := [fil43,fil44,fil65,fil45,fil163,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve608 : Ban 60 6 etat548 := viaCut proj19 petit41 (by decide) (by decide +kernel) (by decide +kernel)
def etat549 : List ℕ := [fil43,fil44,fil65,fil45,fil143,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve609 : Ban 60 6 etat549 := viaPerm proj26 proj26 preuve414 (by decide +kernel) (by decide +kernel)
def etat550 : List ℕ := [fil0,fil1,fil2,fil36,fil41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit49 : Wide 30 4 etat550 := viaSearch (by decide +kernel)
def fil186 : ℕ := 0x618618618618618ffffffffffc0000
def etat551 : List ℕ := [fil42,fil65,fil45,fil46,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve611 : Ban 60 5 etat551 := viaCut proj18 petit49 (by decide) (by decide +kernel) (by decide +kernel)
def fil187 : ℕ := 0x3f000fc0000000
def etat552 : List ℕ := [fil187,fil43,fil44,fil65,fil46,fil125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve612 : Ban 60 5 etat552 := viaCut proj20 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def fil188 : ℕ := 0xfc0000fc0000000
def etat553 : List ℕ := [fil188,fil43,fil44,fil65,fil45,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve613 : Ban 60 5 etat553 := viaCut proj21 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def fil189 : ℕ := 0x410410410410410fffffffc0000000
def etat554 : List ℕ := [fil43,fil44,fil65,fil45,fil46,fil189]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve614 : Ban 60 5 etat554 := viaCut proj20 petit6 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit50 : Wide 30 4 etat368 := viaSub (ws := [etat368])
  (consBan preuve425 (nilBan _ _))
  (by decide) (by decide +kernel)
def etat555 : List ℕ := [fil43,fil44,fil65,fil141,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve615 : Ban 60 5 etat555 := viaCut proj18 petit50 (by decide) (by decide +kernel) (by decide +kernel)
def etat556 : List ℕ := [fil43,fil44,fil97,fil46,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve616 : Ban 60 5 etat556 := viaCut proj20 petit44 (by decide) (by decide +kernel) (by decide +kernel)
def etat557 : List ℕ := [fil43,fil44,fil45,fil142,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve617 : Ban 60 5 etat557 := viaCut proj21 petit44 (by decide) (by decide +kernel) (by decide +kernel)
def fil190 : ℕ := 0x6318c633e000000
def etat558 : List ℕ := [fil0,fil1,fil2,fil3,fil190]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit51 : Wide 30 4 etat558 := viaSearch (by decide +kernel)
def fil191 : ℕ := 0x514514514514514fff000fc0000000
def etat559 : List ℕ := [fil43,fil44,fil45,fil46,fil191,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve618 : Ban 60 5 etat559 := viaCut proj21 petit51 (by decide) (by decide +kernel) (by decide +kernel)
def fil192 : ℕ := 0x618618618618618fff000fc0000000
def etat560 : List ℕ := [fil43,fil44,fil45,fil46,fil125,fil192]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve619 : Ban 60 5 etat560 := viaCut proj20 petit51 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit52 : Wide 30 4 etat348 := viaSearch (by decide +kernel)
def fil193 : ℕ := 0x6db6db6db6db6dbfffffffffffffff
def etat561 : List ℕ := [fil43,fil44,fil45,fil46,fil125,fil193]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve620 : Ban 60 5 etat561 := viaCut proj20 petit52 (by decide) (by decide +kernel) (by decide +kernel)
def etat562 : List ℕ := [fil43,fil44,fil45,fil46,fil123,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve621 : Ban 60 5 etat562 := viaCut proj21 petit52 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit53 : Wide 30 4 etat349 := viaSearch (by decide +kernel)
def etat563 : List ℕ := [fil43,fil44,fil45,fil143,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve622 : Ban 60 5 etat563 := viaCut proj20 petit53 (by decide) (by decide +kernel) (by decide +kernel)
def etat564 : List ℕ := [fil43,fil44,fil102,fil46,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve623 : Ban 60 5 etat564 := viaCut proj21 petit53 (by decide) (by decide +kernel) (by decide +kernel)
def etat565 : List ℕ := [fil0,fil1,fil2,fil36,fil137]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit54 : Wide 30 4 etat565 := viaSearch (by decide +kernel)
def fil194 : ℕ := 0x69a69a69a69a69affffffffffff03f
def etat566 : List ℕ := [fil43,fil65,fil45,fil46,fil125,fil194]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve624 : Ban 60 5 etat566 := viaCut proj18 petit54 (by decide) (by decide +kernel) (by decide +kernel)
def etat567 : List ℕ := [fil0,fil1,fil2,fil34,fil41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit55 : Wide 30 4 etat567 := viaSearch (by decide +kernel)
def fil195 : ℕ := 0x596596596596596fffffffff03ffff
def etat568 : List ℕ := [fil43,fil65,fil45,fil46,fil195,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve625 : Ban 60 5 etat568 := viaCut proj18 petit55 (by decide) (by decide +kernel) (by decide +kernel)
def etat569 : List ℕ := [fil43,fil44,fil121,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve627 : Ban 60 4 etat569 := viaCut proj22 petit52 (by decide) (by decide +kernel) (by decide +kernel)
def etat570 : List ℕ := [fil1,fil21,fil34,fil41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit56 : Wide 30 3 etat570 := viaSearch (by decide +kernel)
def etat571 : List ℕ := [fil43,fil100,fil163,fil195,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve628 : Ban 60 4 etat571 := viaCut proj18 petit56 (by decide) (by decide +kernel) (by decide +kernel)
def etat572 : List ℕ := [fil43,fil102,fil163,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve629 : Ban 60 4 etat572 := viaCut proj21 petit53 (by decide) (by decide +kernel) (by decide +kernel)
def etat573 : List ℕ := [fil9,fil2,fil36,fil137]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit57 : Wide 30 3 etat573 := viaSearch (by decide +kernel)
def fil196 : ℕ := 0x659659659659659ffffffffffc0fff
def etat574 : List ℕ := [fil44,fil100,fil163,fil125,fil196]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve630 : Ban 60 4 etat574 := viaCut proj19 petit57 (by decide) (by decide +kernel) (by decide +kernel)
def etat575 : List ℕ := [fil44,fil100,fil143,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve631 : Ban 60 4 etat575 := viaCut proj20 petit53 (by decide) (by decide +kernel) (by decide +kernel)
def etat576 : List ℕ := [fil65,fil100,fil163,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve632 : Ban 60 4 etat576 := viaBranch (ws := [])
  (nilBan _ _)
  (by decide) (by decide +kernel) (by decide +kernel)
def etat577 : List ℕ := [fil43,fil44,fil100,fil163,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve626 : Ban 60 5 etat577 := viaBranch (ws := [etat569,etat571,etat572,etat574,etat575,etat576])
  (consBan preuve627 (consBan preuve628 (consBan preuve629 (consBan preuve630 (consBan preuve631 (consBan preuve632 (nilBan _ _)))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def proj35 : Projection 60 60 := pick [6,8,7,10,9,11,0,2,1,4,3,5,12,14,13,16,15,17,36,38,37,40,39,41,48,50,49,52,51,53,42,44,43,46,45,47,18,20,19,22,21,23,30,32,31,34,33,35,24,26,25,28,27,29,54,56,55,58,57,59] rfl (by decide +kernel) (by decide)
def etat578 : List ℕ := [fil43,fil65,fil45,fil163,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve633 : Ban 60 5 etat578 := viaPerm proj35 proj35 preuve626 (by decide +kernel) (by decide +kernel)
def proj36 : Projection 60 60 := pick [18,21,19,22,20,23,0,3,1,4,2,5,24,27,25,28,26,29,36,39,37,40,38,41,54,57,55,58,56,59,42,45,43,46,44,47,6,9,7,10,8,11,30,33,31,34,32,35,12,15,13,16,14,17,48,51,49,52,50,53] rfl (by decide +kernel) (by decide)
def proj37 : Projection 60 60 := pick [6,8,10,7,9,11,36,38,40,37,39,41,48,50,52,49,51,53,0,2,4,1,3,5,12,14,16,13,15,17,42,44,46,43,45,47,18,20,22,19,21,23,30,32,34,31,33,35,54,56,58,55,57,59,24,26,28,25,27,29] rfl (by decide +kernel) (by decide)
def etat579 : List ℕ := [fil43,fil65,fil101,fil46,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve634 : Ban 60 5 etat579 := viaPerm proj36 proj37 preuve626 (by decide +kernel) (by decide +kernel)
def etat580 : List ℕ := [fil44,fil65,fil45,fil46,fil125,fil196]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve635 : Ban 60 5 etat580 := viaCut proj19 petit54 (by decide) (by decide +kernel) (by decide +kernel)
def etat581 : List ℕ := [fil44,fil65,fil45,fil46,fil151,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve636 : Ban 60 5 etat581 := viaCut proj19 petit55 (by decide) (by decide +kernel) (by decide +kernel)
def proj38 : Projection 60 60 := pick [13,14,12,16,15,17,1,2,0,4,3,5,7,8,6,10,9,11,43,44,42,46,45,47,49,50,48,52,51,53,37,38,36,40,39,41,25,26,24,28,27,29,31,32,30,34,33,35,19,20,18,22,21,23,55,56,54,58,57,59] rfl (by decide +kernel) (by decide)
def proj39 : Projection 60 60 := pick [8,6,7,10,9,11,14,12,13,16,15,17,2,0,1,4,3,5,50,48,49,52,51,53,38,36,37,40,39,41,44,42,43,46,45,47,32,30,31,34,33,35,20,18,19,22,21,23,26,24,25,28,27,29,56,54,55,58,57,59] rfl (by decide +kernel) (by decide)
def etat582 : List ℕ := [fil44,fil65,fil45,fil164,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve637 : Ban 60 5 etat582 := viaPerm proj38 proj39 preuve626 (by decide +kernel) (by decide +kernel)
def proj40 : Projection 60 60 := pick [25,27,24,28,26,29,1,3,0,4,2,5,19,21,18,22,20,23,43,45,42,46,44,47,55,57,54,58,56,59,37,39,36,40,38,41,13,15,12,16,14,17,31,33,30,34,32,35,7,9,6,10,8,11,49,51,48,52,50,53] rfl (by decide +kernel) (by decide)
def proj41 : Projection 60 60 := pick [8,6,10,7,9,11,50,48,52,49,51,53,38,36,40,37,39,41,14,12,16,13,15,17,2,0,4,1,3,5,44,42,46,43,45,47,32,30,34,31,33,35,20,18,22,19,21,23,56,54,58,55,57,59,26,24,28,25,27,29] rfl (by decide +kernel) (by decide)
def etat583 : List ℕ := [fil44,fil65,fil100,fil46,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve638 : Ban 60 5 etat583 := viaPerm proj40 proj41 preuve626 (by decide +kernel) (by decide +kernel)
def etat584 : List ℕ := [fil43,fil44,fil65,fil45,fil46,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve610 : Ban 60 6 etat584 := viaBranch (ws := [etat551,etat552,etat553,etat554,etat555,etat556,etat557,etat559,etat560,etat561,etat562,etat563,etat564,etat566,etat568,etat578,etat579,etat580,etat581,etat582,etat583])
  (consBan preuve611 (consBan preuve612 (consBan preuve613 (consBan preuve614 (consBan preuve615 (consBan preuve616 (consBan preuve617 (consBan preuve618 (consBan preuve619 (consBan preuve620 (consBan preuve621 (consBan preuve622 (consBan preuve623 (consBan preuve624 (consBan preuve625 (consBan preuve633 (consBan preuve634 (consBan preuve635 (consBan preuve636 (consBan preuve637 (consBan preuve638 (nilBan _ _))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def etat585 : List ℕ := [fil43,fil44,fil65,fil45,fil141,fil47,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve639 : Ban 60 6 etat585 := viaPerm proj26 proj26 preuve610 (by decide +kernel) (by decide +kernel)
def etat586 : List ℕ := [fil43,fil44,fil65,fil100,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve640 : Ban 60 6 etat586 := viaCut proj18 petit41 (by decide) (by decide +kernel) (by decide +kernel)
def etat587 : List ℕ := [fil43,fil44,fil65,fil101,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve641 : Ban 60 6 etat587 := viaCut proj19 petit41 (by decide) (by decide +kernel) (by decide +kernel)
def etat588 : List ℕ := [fil43,fil44,fil65,fil166,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve642 : Ban 60 6 etat588 := viaCut proj21 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def etat589 : List ℕ := [fil43,fil44,fil65,fil46,fil141,fil47,fil125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve643 : Ban 60 6 etat589 := viaPerm proj23 proj24 preuve610 (by decide +kernel) (by decide +kernel)
def etat590 : List ℕ := [fil43,fil44,fil97,fil45,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve644 : Ban 60 6 etat590 := viaCut proj20 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def etat591 : List ℕ := [fil43,fil44,fil97,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve645 : Ban 60 6 etat591 := viaCut proj20 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat592 : List ℕ := [fil43,fil44,fil45,fil102,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve646 : Ban 60 6 etat592 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat593 : List ℕ := [fil43,fil44,fil45,fil142,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve647 : Ban 60 6 etat593 := viaCut proj21 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def etat594 : List ℕ := [fil43,fil44,fil45,fil142,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve648 : Ban 60 6 etat594 := viaCut proj21 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat595 : List ℕ := [fil43,fil44,fil45,fil46,fil143,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve649 : Ban 60 6 etat595 := viaCut proj21 petit2 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve650 : Ban 30 5 etat47 := viaPerm proj7 proj7 preuve177 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit58 : Wide 30 5 etat47 := viaSub (ws := [etat0,etat47])
  (consBan preuve93 (consBan preuve650 (nilBan _ _)))
  (by decide) (by decide +kernel)
def etat596 : List ℕ := [fil43,fil44,fil45,fil46,fil178,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve651 : Ban 60 6 etat596 := viaCut proj20 petit58 (by decide) (by decide +kernel) (by decide +kernel)
def etat597 : List ℕ := [fil43,fil44,fil45,fil46,fil178,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve652 : Ban 60 6 etat597 := viaCut proj20 petit58 (by decide) (by decide +kernel) (by decide +kernel)
def etat598 : List ℕ := [fil43,fil44,fil45,fil46,fil141,fil121,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve653 : Ban 60 6 etat598 := viaCut proj20 petit15 (by decide) (by decide +kernel) (by decide +kernel)
def etat599 : List ℕ := [fil43,fil44,fil45,fil46,fil141,fil130,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve654 : Ban 60 6 etat599 := viaCut proj22 petit44 (by decide) (by decide +kernel) (by decide +kernel)
def etat600 : List ℕ := [fil43,fil44,fil45,fil46,fil141,fil47,fil124]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve655 : Ban 60 6 etat600 := viaCut proj20 petit16 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve656 : Ban 60 6 etat408 := viaCut proj18 petit15 (by decide) (by decide +kernel) (by decide +kernel)
def etat601 : List ℕ := [fil43,fil44,fil45,fil143,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve657 : Ban 60 6 etat601 := viaCut proj20 petit15 (by decide) (by decide +kernel) (by decide +kernel)
def etat602 : List ℕ := [fil43,fil44,fil102,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve658 : Ban 60 6 etat602 := viaCut proj21 petit15 (by decide) (by decide +kernel) (by decide +kernel)
def etat603 : List ℕ := [fil43,fil65,fil45,fil101,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve659 : Ban 60 6 etat603 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat604 : List ℕ := [fil43,fil65,fil45,fil46,fil163,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve660 : Ban 60 6 etat604 := viaCut proj21 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def proj42 : Projection 60 60 := pick [32,33,30,34,31,35,8,9,6,10,7,11,20,21,18,22,19,23,50,51,48,52,49,53,56,57,54,58,55,59,38,39,36,40,37,41,14,15,12,16,13,17,26,27,24,28,25,29,2,3,0,4,1,5,44,45,42,46,43,47] rfl (by decide +kernel) (by decide)
def proj43 : Projection 60 60 := pick [50,52,48,49,51,53,8,10,6,7,9,11,38,40,36,37,39,41,14,16,12,13,15,17,44,46,42,43,45,47,2,4,0,1,3,5,32,34,30,31,33,35,56,58,54,55,57,59,20,22,18,19,21,23,26,28,24,25,27,29] rfl (by decide +kernel) (by decide)
def etat605 : List ℕ := [fil43,fil65,fil45,fil46,fil141,fil182,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve661 : Ban 60 6 etat605 := viaPerm proj42 proj43 preuve414 (by decide +kernel) (by decide +kernel)
def etat606 : List ℕ := [fil43,fil65,fil45,fil46,fil141,fil47,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve662 : Ban 60 6 etat606 := viaPerm proj42 proj43 preuve610 (by decide +kernel) (by decide +kernel)
def etat607 : List ℕ := [fil43,fil65,fil45,fil46,fil182,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve663 : Ban 60 6 etat607 := viaCut proj18 petit15 (by decide) (by decide +kernel) (by decide +kernel)
def etat608 : List ℕ := [fil0,fil1,fil2,fil20,fil41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit59 : Wide 30 4 etat608 := viaSearch (by decide +kernel)
def fil197 : ℕ := 0x3f000fc0000
def etat609 : List ℕ := [fil197,fil44,fil45,fil164,fil153,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve665 : Ban 60 5 etat609 := viaCut proj18 petit59 (by decide) (by decide +kernel) (by decide +kernel)
def etat610 : List ℕ := [fil0,fil1,fil21,fil3,fil41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit60 : Wide 30 4 etat610 := viaSearch (by decide +kernel)
def fil198 : ℕ := 0xfc003f000000
def etat611 : List ℕ := [fil198,fil43,fil45,fil164,fil153,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve666 : Ban 60 5 etat611 := viaCut proj19 petit60 (by decide) (by decide +kernel) (by decide +kernel)
def fil199 : ℕ := 0x3e0003e0
def etat612 : List ℕ := [fil199,fil0,fil1,fil2,fil41]
def etat613 : List ℕ := [fil199,fil0,fil1,fil41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve667 : Ban 30 4 etat613 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve668 : Ban 30 4 etat612 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit61 : Wide 30 4 etat612 := viaSub (ws := [etat613,etat612])
  (consBan preuve667 (consBan preuve668 (nilBan _ _)))
  (by decide) (by decide +kernel)
def fil200 : ℕ := 0xfc003f03f00003f
def etat614 : List ℕ := [fil200,fil43,fil44,fil45,fil164,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve669 : Ban 60 5 etat614 := viaCut proj18 petit61 (by decide) (by decide +kernel) (by decide +kernel)
def fil201 : ℕ := 0x3e0f8000
def etat615 : List ℕ := [fil201,fil0,fil1,fil3,fil41]
def etat616 : List ℕ := [fil201,fil0,fil1,fil41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve670 : Ban 30 4 etat616 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve671 : Ban 30 4 etat615 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit62 : Wide 30 4 etat615 := viaSub (ws := [etat616,etat615])
  (consBan preuve670 (consBan preuve671 (nilBan _ _)))
  (by decide) (by decide +kernel)
def etat617 : List ℕ := [fil200,fil43,fil44,fil45,fil153,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve672 : Ban 60 5 etat617 := viaCut proj19 petit62 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit63 : Wide 30 4 etat613 := viaSearch (by decide +kernel)
def etat618 : List ℕ := [fil200,fil43,fil44,fil45,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve673 : Ban 60 5 etat618 := viaCut proj18 petit63 (by decide) (by decide +kernel) (by decide +kernel)
def fil202 : ℕ := 0x41041041041041000000000fc0fc0
def etat619 : List ℕ := [fil202,fil44,fil45,fil164,fil153,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve674 : Ban 60 5 etat619 := viaCut proj18 petit59 (by decide) (by decide +kernel) (by decide +kernel)
def etat620 : List ℕ := [fil59,fil44,fil45,fil164,fil153,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve675 : Ban 60 5 etat620 := viaCut proj18 petit59 (by decide) (by decide +kernel) (by decide +kernel)
def etat621 : List ℕ := [fil60,fil44,fil45,fil164,fil153,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve676 : Ban 60 5 etat621 := viaCut proj18 petit59 (by decide) (by decide +kernel) (by decide +kernel)
def fil203 : ℕ := 0x82082082082082000fc000003f000
def etat622 : List ℕ := [fil43,fil203,fil45,fil164,fil153,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve677 : Ban 60 5 etat622 := viaCut proj19 petit60 (by decide) (by decide +kernel) (by decide +kernel)
def etat623 : List ℕ := [fil43,fil63,fil45,fil164,fil153,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve678 : Ban 60 5 etat623 := viaCut proj19 petit60 (by decide) (by decide +kernel) (by decide +kernel)
def etat624 : List ℕ := [fil43,fil64,fil45,fil164,fil153,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve679 : Ban 60 5 etat624 := viaCut proj18 petit59 (by decide) (by decide +kernel) (by decide +kernel)
def fil204 : ℕ := 0x208208208208208000000fc0fc0000
def etat625 : List ℕ := [fil43,fil44,fil45,fil204,fil164,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve680 : Ban 60 5 etat625 := viaCut proj21 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def etat626 : List ℕ := [fil43,fil44,fil45,fil168,fil153,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve681 : Ban 60 5 etat626 := viaCut proj21 petit30 (by decide) (by decide +kernel) (by decide +kernel)
def fil205 : ℕ := 0x208208208208208fc003fffffc0000
def etat627 : List ℕ := [fil43,fil44,fil45,fil205,fil153,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve682 : Ban 60 5 etat627 := viaCut proj22 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def fil206 : ℕ := 0x210842100007c00
def etat628 : List ℕ := [fil0,fil1,fil206,fil2,fil41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit64 : Wide 30 4 etat628 := viaSearch (by decide +kernel)
def fil207 : ℕ := 0x249249249249249000000fc0fc0fc0
def etat629 : List ℕ := [fil43,fil44,fil45,fil207,fil164,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve683 : Ban 60 5 etat629 := viaCut proj18 petit64 (by decide) (by decide +kernel) (by decide +kernel)
def etat630 : List ℕ := [fil0,fil1,fil117,fil3,fil41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit65 : Wide 30 4 etat630 := viaSearch (by decide +kernel)
def fil208 : ℕ := 0x249249249249249fc003f03ffc003f
def etat631 : List ℕ := [fil43,fil44,fil45,fil208,fil153,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve684 : Ban 60 5 etat631 := viaCut proj19 petit65 (by decide) (by decide +kernel) (by decide +kernel)
def fil209 : ℕ := 0x249249249249249fc003ffc0fc0fc0
def etat632 : List ℕ := [fil43,fil44,fil45,fil209,fil153,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve685 : Ban 60 5 etat632 := viaCut proj19 petit60 (by decide) (by decide +kernel) (by decide +kernel)
def fil210 : ℕ := 0x410410410410410fff03f000000000
def etat633 : List ℕ := [fil43,fil44,fil45,fil164,fil210,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve686 : Ban 60 5 etat633 := viaCut proj22 petit31 (by decide) (by decide +kernel) (by decide +kernel)
def fil211 : ℕ := 0x410410410410410ffffff03f000000
def etat634 : List ℕ := [fil43,fil44,fil45,fil164,fil211,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve687 : Ban 60 5 etat634 := viaCut proj21 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat635 : List ℕ := [fil0,fil1,fil2,fil159,fil41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit66 : Wide 30 4 etat635 := viaSearch (by decide +kernel)
def fil212 : ℕ := 0x492492492492492fc0fff03f00003f
def etat636 : List ℕ := [fil43,fil44,fil45,fil164,fil212,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve688 : Ban 60 5 etat636 := viaCut proj18 petit66 (by decide) (by decide +kernel) (by decide +kernel)
def etat637 : List ℕ := [fil43,fil44,fil45,fil164,fil140,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve689 : Ban 60 5 etat637 := viaCut proj18 petit59 (by decide) (by decide +kernel) (by decide +kernel)
def fil213 : ℕ := 0x6318c633e0f83e0
def etat638 : List ℕ := [fil0,fil1,fil2,fil20,fil213]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit67 : Wide 30 4 etat638 := viaSearch (by decide +kernel)
def fil214 : ℕ := 0x618618618618618fc0fff03ffc0000
def etat639 : List ℕ := [fil43,fil44,fil45,fil164,fil153,fil214]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve690 : Ban 60 5 etat639 := viaCut proj18 petit67 (by decide) (by decide +kernel) (by decide +kernel)
def etat640 : List ℕ := [fil0,fil1,fil2,fil20,fil184]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit68 : Wide 30 4 etat640 := viaSearch (by decide +kernel)
def etat641 : List ℕ := [fil43,fil44,fil45,fil164,fil153,fil185]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve691 : Ban 60 5 etat641 := viaCut proj18 petit68 (by decide) (by decide +kernel) (by decide +kernel)
def etat642 : List ℕ := [fil43,fil44,fil45,fil164,fil124,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve692 : Ban 60 5 etat642 := viaCut proj18 petit59 (by decide) (by decide +kernel) (by decide +kernel)
def etat643 : List ℕ := [fil43,fil44,fil45,fil164,fil195,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve693 : Ban 60 5 etat643 := viaCut proj18 petit55 (by decide) (by decide +kernel) (by decide +kernel)
def etat644 : List ℕ := [fil43,fil44,fil45,fil143,fil153,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve694 : Ban 60 5 etat644 := viaCut proj19 petit60 (by decide) (by decide +kernel) (by decide +kernel)
def etat645 : List ℕ := [fil43,fil44,fil45,fil181,fil153,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve695 : Ban 60 5 etat645 := viaCut proj19 petit53 (by decide) (by decide +kernel) (by decide +kernel)
def fil215 : ℕ := 0x41041041041041003ffc0000000000
def etat646 : List ℕ := [fil43,fil44,fil45,fil215,fil153,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve696 : Ban 60 5 etat646 := viaCut proj22 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def fil216 : ℕ := 0x421084201f00000
def etat647 : List ℕ := [fil0,fil1,fil216,fil3,fil41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit69 : Wide 30 4 etat647 := viaSearch (by decide +kernel)
def fil217 : ℕ := 0x49249249249249203ffc000003f000
def etat648 : List ℕ := [fil43,fil44,fil45,fil217,fil153,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve697 : Ban 60 5 etat648 := viaCut proj19 petit69 (by decide) (by decide +kernel) (by decide +kernel)
def etat649 : List ℕ := [fil43,fil65,fil45,fil164,fil153,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve698 : Ban 60 5 etat649 := viaCut proj18 petit59 (by decide) (by decide +kernel) (by decide +kernel)
def proj44 : Projection 60 60 := pick [6,8,9,7,10,11,18,20,21,19,22,23,30,32,33,31,34,35,0,2,3,1,4,5,12,14,15,13,16,17,24,26,27,25,28,29,36,38,39,37,40,41,48,50,51,49,52,53,54,56,57,55,58,59,42,44,45,43,46,47] rfl (by decide +kernel) (by decide)
def proj45 : Projection 60 60 := pick [18,21,19,20,22,23,0,3,1,2,4,5,24,27,25,26,28,29,6,9,7,8,10,11,30,33,31,32,34,35,12,15,13,14,16,17,36,39,37,38,40,41,54,57,55,56,58,59,42,45,43,44,46,47,48,51,49,50,52,53] rfl (by decide +kernel) (by decide)
def etat650 : List ℕ := [fil43,fil45,fil101,fil164,fil153,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve699 : Ban 60 5 etat650 := viaPerm proj44 proj45 preuve626 (by decide +kernel) (by decide +kernel)
def etat651 : List ℕ := [fil1,fil2,fil21,fil20,fil41]
def etat652 : List ℕ := [fil1,fil21,fil20,fil41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve700 : Ban 30 4 etat652 := viaPerm proj9 proj9 preuve425 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve701 : Ban 30 4 etat651 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit70 : Wide 30 4 etat651 := viaSub (ws := [etat652,etat651])
  (consBan preuve700 (consBan preuve701 (nilBan _ _)))
  (by decide) (by decide +kernel)
def etat653 : List ℕ := [fil43,fil45,fil164,fil143,fil153,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve702 : Ban 60 5 etat653 := viaCut proj18 petit70 (by decide) (by decide +kernel) (by decide +kernel)
def etat654 : List ℕ := [fil43,fil45,fil164,fil210,fil153,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve703 : Ban 60 5 etat654 := viaCut proj22 petit31 (by decide) (by decide +kernel) (by decide +kernel)
def etat655 : List ℕ := [fil1,fil2,fil20,fil136,fil41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit71 : Wide 30 4 etat655 := viaSearch (by decide +kernel)
def fil218 : ℕ := 0x618618618618618fff03ffc0fc0000
def etat656 : List ℕ := [fil43,fil45,fil164,fil153,fil218,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve704 : Ban 60 5 etat656 := viaCut proj18 petit71 (by decide) (by decide +kernel) (by decide +kernel)
def etat657 : List ℕ := [fil43,fil45,fil143,fil153,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve705 : Ban 60 5 etat657 := viaCut proj22 petit16 (by decide) (by decide +kernel) (by decide +kernel)
def etat658 : List ℕ := [fil44,fil65,fil45,fil164,fil153,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve706 : Ban 60 5 etat658 := viaCut proj19 petit60 (by decide) (by decide +kernel) (by decide +kernel)
def proj46 : Projection 60 60 := pick [13,14,16,12,15,17,43,44,46,42,45,47,49,50,52,48,51,53,1,2,4,0,3,5,7,8,10,6,9,11,37,38,40,36,39,41,25,26,28,24,27,29,31,32,34,30,33,35,55,56,58,54,57,59,19,20,22,18,21,23] rfl (by decide +kernel) (by decide)
def proj47 : Projection 60 60 := pick [21,18,19,22,20,23,27,24,25,28,26,29,3,0,1,4,2,5,57,54,55,58,56,59,39,36,37,40,38,41,45,42,43,46,44,47,33,30,31,34,32,35,9,6,7,10,8,11,15,12,13,16,14,17,51,48,49,52,50,53] rfl (by decide +kernel) (by decide)
def etat659 : List ℕ := [fil44,fil45,fil100,fil164,fil153,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve707 : Ban 60 5 etat659 := viaPerm proj46 proj47 preuve626 (by decide +kernel) (by decide +kernel)
def etat660 : List ℕ := [fil44,fil45,fil168,fil164,fil153,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve708 : Ban 60 5 etat660 := viaCut proj21 petit30 (by decide) (by decide +kernel) (by decide +kernel)
def etat661 : List ℕ := [fil1,fil21,fil3,fil20,fil41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve709 : Ban 30 4 etat661 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit72 : Wide 30 4 etat661 := viaSub (ws := [etat652,etat661])
  (consBan preuve700 (consBan preuve709 (nilBan _ _)))
  (by decide) (by decide +kernel)
def etat662 : List ℕ := [fil44,fil45,fil164,fil153,fil124,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve710 : Ban 60 5 etat662 := viaCut proj19 petit72 (by decide) (by decide +kernel) (by decide +kernel)
def etat663 : List ℕ := [fil1,fil21,fil3,fil136,fil41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit73 : Wide 30 4 etat663 := viaSearch (by decide +kernel)
def fil219 : ℕ := 0x618618618618618ffffc0fff000000
def etat664 : List ℕ := [fil44,fil45,fil164,fil153,fil219,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve711 : Ban 60 5 etat664 := viaCut proj19 petit73 (by decide) (by decide +kernel) (by decide +kernel)
def etat665 : List ℕ := [fil44,fil45,fil164,fil124,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve712 : Ban 60 5 etat665 := viaCut proj21 petit16 (by decide) (by decide +kernel) (by decide +kernel)
def fil220 : ℕ := 0x1f07c00
def etat666 : List ℕ := [fil220,fil0,fil1,fil2,fil36]
def etat667 : List ℕ := [fil220,fil0,fil2,fil36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve714 : Ban 30 4 etat667 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve715 : Ban 30 4 etat666 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit74 : Wide 30 4 etat666 := viaSub (ws := [etat667,etat666])
  (consBan preuve714 (consBan preuve715 (nilBan _ _)))
  (by decide) (by decide +kernel)
def fil221 : ℕ := 0x3ffc0fff000000
def etat668 : List ℕ := [fil221,fil43,fil101,fil163,fil125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve716 : Ban 60 4 etat668 := viaCut proj19 petit74 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit75 : Wide 30 4 etat667 := viaSearch (by decide +kernel)
def etat669 : List ℕ := [fil221,fil43,fil163,fil125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve717 : Ban 60 4 etat669 := viaCut proj19 petit75 (by decide) (by decide +kernel) (by decide +kernel)
def etat670 : List ℕ := [fil82,fil0,fil1,fil3,fil41]
def etat671 : List ℕ := [fil82,fil0,fil1,fil41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve718 : Ban 30 4 etat671 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve719 : Ban 30 4 etat670 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit76 : Wide 30 4 etat670 := viaSub (ws := [etat671,etat670])
  (consBan preuve718 (consBan preuve719 (nilBan _ _)))
  (by decide) (by decide +kernel)
def etat672 : List ℕ := [fil221,fil43,fil163,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve720 : Ban 60 4 etat672 := viaCut proj21 petit76 (by decide) (by decide +kernel) (by decide +kernel)
def etat673 : List ℕ := [fil220,fil0,fil1,fil35,fil3]
def etat674 : List ℕ := [fil220,fil0,fil35,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve721 : Ban 30 4 etat674 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve722 : Ban 30 4 etat673 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit77 : Wide 30 4 etat673 := viaSub (ws := [etat674,etat673])
  (consBan preuve721 (consBan preuve722 (nilBan _ _)))
  (by decide) (by decide +kernel)
def fil222 : ℕ := 0xfc0fc0fc003f000
def etat675 : List ℕ := [fil222,fil43,fil101,fil163,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve723 : Ban 60 4 etat675 := viaCut proj21 petit77 (by decide) (by decide +kernel) (by decide +kernel)
def fil223 : ℕ := 0x3e007c00
def etat676 : List ℕ := [fil223,fil0,fil2,fil35,fil3]
def etat677 : List ℕ := [fil223,fil0,fil35,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve724 : Ban 30 4 etat677 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve725 : Ban 30 4 etat676 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit78 : Wide 30 4 etat676 := viaSub (ws := [etat677,etat676])
  (consBan preuve724 (consBan preuve725 (nilBan _ _)))
  (by decide) (by decide +kernel)
def etat678 : List ℕ := [fil222,fil43,fil101,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve726 : Ban 60 4 etat678 := viaCut proj22 petit78 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit79 : Wide 30 4 etat674 := viaSearch (by decide +kernel)
def etat679 : List ℕ := [fil222,fil43,fil101,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve727 : Ban 60 4 etat679 := viaCut proj21 petit79 (by decide) (by decide +kernel) (by decide +kernel)
def etat680 : List ℕ := [fil0,fil131,fil1,fil2,fil36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit80 : Wide 30 4 etat680 := viaSearch (by decide +kernel)
def fil224 : ℕ := 0x18618618618618600000000003ffff
def etat681 : List ℕ := [fil43,fil224,fil101,fil163,fil125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve728 : Ban 60 4 etat681 := viaCut proj19 petit80 (by decide) (by decide +kernel) (by decide +kernel)
def etat682 : List ℕ := [fil0,fil1,fil84,fil3,fil41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit81 : Wide 30 4 etat682 := viaSearch (by decide +kernel)
def etat683 : List ℕ := [fil43,fil106,fil163,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve729 : Ban 60 4 etat683 := viaCut proj21 petit81 (by decide) (by decide +kernel) (by decide +kernel)
def etat684 : List ℕ := [fil0,fil131,fil1,fil35,fil3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit82 : Wide 30 4 etat684 := viaSearch (by decide +kernel)
def fil225 : ℕ := 0x28a28a28a28a28a00000003ffc003f
def etat685 : List ℕ := [fil43,fil101,fil225,fil163,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve730 : Ban 60 4 etat685 := viaCut proj21 petit82 (by decide) (by decide +kernel) (by decide +kernel)
def fil226 : ℕ := 0x28a28a28a28a28afc0fc0fff03f000
def etat686 : List ℕ := [fil43,fil101,fil226,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve731 : Ban 60 4 etat686 := viaCut proj20 petit81 (by decide) (by decide +kernel) (by decide +kernel)
def etat687 : List ℕ := [fil0,fil1,fil2,fil88,fil41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit83 : Wide 30 4 etat687 := viaSearch (by decide +kernel)
def etat688 : List ℕ := [fil43,fil101,fil163,fil162,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve732 : Ban 60 4 etat688 := viaCut proj19 petit83 (by decide) (by decide +kernel) (by decide +kernel)
def etat689 : List ℕ := [fil0,fil1,fil2,fil36,fil136]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit84 : Wide 30 4 etat689 := viaSearch (by decide +kernel)
def etat690 : List ℕ := [fil43,fil101,fil163,fil125,fil219]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve733 : Ban 60 4 etat690 := viaCut proj19 petit84 (by decide) (by decide +kernel) (by decide +kernel)
def etat691 : List ℕ := [fil43,fil101,fil163,fil125,fil196]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve734 : Ban 60 4 etat691 := viaCut proj19 petit54 (by decide) (by decide +kernel) (by decide +kernel)
def etat692 : List ℕ := [fil43,fil101,fil163,fil151,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve735 : Ban 60 4 etat692 := viaCut proj19 petit55 (by decide) (by decide +kernel) (by decide +kernel)
def etat693 : List ℕ := [fil43,fil101,fil143,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve736 : Ban 60 4 etat693 := viaCut proj20 petit53 (by decide) (by decide +kernel) (by decide +kernel)
def etat694 : List ℕ := [fil0,fil1,fil138,fil3,fil41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit85 : Wide 30 4 etat694 := viaSearch (by decide +kernel)
def fil227 : ℕ := 0x51451451451451403f03f000000fc0
def etat695 : List ℕ := [fil43,fil101,fil227,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve737 : Ban 60 4 etat695 := viaCut proj20 petit85 (by decide) (by decide +kernel) (by decide +kernel)
def fil228 : ℕ := 0x618618618618618fc003f000fc0000
def etat696 : List ℕ := [fil43,fil163,fil125,fil228,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve738 : Ban 60 4 etat696 := viaCut proj21 petit85 (by decide) (by decide +kernel) (by decide +kernel)
def etat697 : List ℕ := [fil43,fil101,fil163,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve713 : Ban 60 5 etat697 := viaBranch (ws := [etat668,etat669,etat672,etat675,etat678,etat679,etat681,etat683,etat685,etat686,etat688,etat690,etat691,etat692,etat693,etat695,etat572,etat696])
  (consBan preuve716 (consBan preuve717 (consBan preuve720 (consBan preuve723 (consBan preuve726 (consBan preuve727 (consBan preuve728 (consBan preuve729 (consBan preuve730 (consBan preuve731 (consBan preuve732 (consBan preuve733 (consBan preuve734 (consBan preuve735 (consBan preuve736 (consBan preuve737 (consBan preuve629 (consBan preuve738 (nilBan _ _)))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def proj48 : Projection 60 60 := pick [8,6,7,9,10,11,14,12,13,15,16,17,2,0,1,3,4,5,32,30,31,33,34,35,20,18,19,21,22,23,26,24,25,27,28,29,50,48,49,51,52,53,38,36,37,39,40,41,44,42,43,45,46,47,56,54,55,57,58,59] rfl (by decide +kernel) (by decide)
def proj49 : Projection 60 60 := pick [13,14,12,15,16,17,1,2,0,3,4,5,7,8,6,9,10,11,25,26,24,27,28,29,31,32,30,33,34,35,19,20,18,21,22,23,43,44,42,45,46,47,49,50,48,51,52,53,37,38,36,39,40,41,55,56,54,57,58,59] rfl (by decide +kernel) (by decide)
def etat698 : List ℕ := [fil65,fil45,fil164,fil153,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve739 : Ban 60 5 etat698 := viaPerm proj48 proj49 preuve713 (by decide +kernel) (by decide +kernel)
def etat699 : List ℕ := [fil43,fil44,fil45,fil164,fil153,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve664 : Ban 60 6 etat699 := viaBranch (ws := [etat609,etat611,etat614,etat617,etat618,etat619,etat620,etat621,etat622,etat623,etat624,etat625,etat626,etat627,etat629,etat631,etat632,etat633,etat634,etat636,etat637,etat639,etat641,etat642,etat643,etat644,etat645,etat646,etat648,etat649,etat650,etat653,etat654,etat656,etat657,etat658,etat659,etat660,etat662,etat664,etat665,etat698])
  (consBan preuve665 (consBan preuve666 (consBan preuve669 (consBan preuve672 (consBan preuve673 (consBan preuve674 (consBan preuve675 (consBan preuve676 (consBan preuve677 (consBan preuve678 (consBan preuve679 (consBan preuve680 (consBan preuve681 (consBan preuve682 (consBan preuve683 (consBan preuve684 (consBan preuve685 (consBan preuve686 (consBan preuve687 (consBan preuve688 (consBan preuve689 (consBan preuve690 (consBan preuve691 (consBan preuve692 (consBan preuve693 (consBan preuve694 (consBan preuve695 (consBan preuve696 (consBan preuve697 (consBan preuve698 (consBan preuve699 (consBan preuve702 (consBan preuve703 (consBan preuve704 (consBan preuve705 (consBan preuve706 (consBan preuve707 (consBan preuve708 (consBan preuve710 (consBan preuve711 (consBan preuve712 (consBan preuve739 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def etat700 : List ℕ := [fil43,fil65,fil45,fil163,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve740 : Ban 60 6 etat700 := viaPerm proj37 proj36 preuve664 (by decide +kernel) (by decide +kernel)
def proj50 : Projection 60 60 := pick [18,21,22,19,20,23,36,39,40,37,38,41,54,57,58,55,56,59,0,3,4,1,2,5,24,27,28,25,26,29,42,45,46,43,44,47,6,9,10,7,8,11,30,33,34,31,32,35,48,51,52,49,50,53,12,15,16,13,14,17] rfl (by decide +kernel) (by decide)
def etat701 : List ℕ := [fil43,fil65,fil101,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve741 : Ban 60 6 etat701 := viaPerm proj50 proj50 preuve664 (by decide +kernel) (by decide +kernel)
def etat702 : List ℕ := [fil64,fil44,fil65,fil45,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve742 : Ban 60 6 etat702 := viaCut proj19 petit40 (by decide) (by decide +kernel) (by decide +kernel)
def etat703 : List ℕ := [fil44,fil65,fil45,fil100,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve743 : Ban 60 6 etat703 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat704 : List ℕ := [fil44,fil65,fil45,fil46,fil164,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve744 : Ban 60 6 etat704 := viaCut proj21 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def proj51 : Projection 60 60 := pick [32,33,31,34,30,35,14,15,13,16,12,17,26,27,25,28,24,29,50,51,49,52,48,53,56,57,55,58,54,59,44,45,43,46,42,47,8,9,7,10,6,11,20,21,19,22,18,23,2,3,1,4,0,5,38,39,37,40,36,41] rfl (by decide +kernel) (by decide)
def proj52 : Projection 60 60 := pick [52,50,48,49,51,53,40,38,36,37,39,41,10,8,6,7,9,11,46,44,42,43,45,47,16,14,12,13,15,17,4,2,0,1,3,5,58,56,54,55,57,59,34,32,30,31,33,35,22,20,18,19,21,23,28,26,24,25,27,29] rfl (by decide +kernel) (by decide)
def etat705 : List ℕ := [fil44,fil65,fil45,fil46,fil141,fil181,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve745 : Ban 60 6 etat705 := viaPerm proj51 proj52 preuve414 (by decide +kernel) (by decide +kernel)
def etat706 : List ℕ := [fil44,fil65,fil45,fil46,fil141,fil47,fil150]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve746 : Ban 60 6 etat706 := viaPerm proj51 proj52 preuve610 (by decide +kernel) (by decide +kernel)
def etat707 : List ℕ := [fil44,fil65,fil45,fil46,fil181,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve747 : Ban 60 6 etat707 := viaCut proj19 petit15 (by decide) (by decide +kernel) (by decide +kernel)
def etat708 : List ℕ := [fil44,fil65,fil45,fil164,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve748 : Ban 60 6 etat708 := viaPerm proj46 proj47 preuve664 (by decide +kernel) (by decide +kernel)
def proj53 : Projection 60 60 := pick [25,27,28,24,26,29,43,45,46,42,44,47,55,57,58,54,56,59,1,3,4,0,2,5,19,21,22,18,20,23,37,39,40,36,38,41,13,15,16,12,14,17,31,33,34,30,32,35,49,51,52,48,50,53,7,9,10,6,8,11] rfl (by decide +kernel) (by decide)
def proj54 : Projection 60 60 := pick [21,18,22,19,20,23,57,54,58,55,56,59,39,36,40,37,38,41,27,24,28,25,26,29,3,0,4,1,2,5,45,42,46,43,44,47,33,30,34,31,32,35,9,6,10,7,8,11,51,48,52,49,50,53,15,12,16,13,14,17] rfl (by decide +kernel) (by decide)
def etat709 : List ℕ := [fil44,fil65,fil100,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve749 : Ban 60 6 etat709 := viaPerm proj53 proj54 preuve664 (by decide +kernel) (by decide +kernel)
def etat710 : List ℕ := [fil43,fil44,fil65,fil45,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve506 : Ban 60 7 etat710 := viaBranch (ws := [etat455,etat456,etat457,etat458,etat459,etat460,etat461,etat499,etat500,etat501,etat502,etat503,etat504,etat505,etat506,etat507,etat508,etat509,etat510,etat511,etat512,etat513,etat514,etat515,etat516,etat517,etat518,etat519,etat520,etat521,etat522,etat523,etat524,etat525,etat526,etat527,etat528,etat276,etat529,etat530,etat531,etat532,etat533,etat448,etat534,etat535,etat536,etat538,etat539,etat540,etat541,etat542,etat543,etat354,etat544,etat546,etat547,etat548,etat549,etat585,etat586,etat587,etat394,etat588,etat589,etat590,etat591,etat592,etat593,etat594,etat595,etat596,etat597,etat598,etat599,etat600,etat408,etat601,etat602,etat603,etat604,etat605,etat606,etat607,etat700,etat701,etat702,etat703,etat704,etat705,etat706,etat707,etat708,etat709])
  (consBan preuve507 (consBan preuve508 (consBan preuve509 (consBan preuve510 (consBan preuve511 (consBan preuve512 (consBan preuve513 (consBan preuve554 (consBan preuve556 (consBan preuve557 (consBan preuve558 (consBan preuve559 (consBan preuve560 (consBan preuve561 (consBan preuve562 (consBan preuve563 (consBan preuve564 (consBan preuve565 (consBan preuve566 (consBan preuve567 (consBan preuve568 (consBan preuve569 (consBan preuve570 (consBan preuve571 (consBan preuve572 (consBan preuve573 (consBan preuve574 (consBan preuve575 (consBan preuve576 (consBan preuve577 (consBan preuve578 (consBan preuve580 (consBan preuve581 (consBan preuve582 (consBan preuve583 (consBan preuve584 (consBan preuve585 (consBan preuve586 (consBan preuve587 (consBan preuve588 (consBan preuve589 (consBan preuve590 (consBan preuve591 (consBan preuve592 (consBan preuve593 (consBan preuve594 (consBan preuve595 (consBan preuve597 (consBan preuve599 (consBan preuve600 (consBan preuve601 (consBan preuve602 (consBan preuve603 (consBan preuve410 (consBan preuve604 (consBan preuve606 (consBan preuve607 (consBan preuve608 (consBan preuve609 (consBan preuve639 (consBan preuve640 (consBan preuve641 (consBan preuve450 (consBan preuve642 (consBan preuve643 (consBan preuve644 (consBan preuve645 (consBan preuve646 (consBan preuve647 (consBan preuve648 (consBan preuve649 (consBan preuve651 (consBan preuve652 (consBan preuve653 (consBan preuve654 (consBan preuve655 (consBan preuve656 (consBan preuve657 (consBan preuve658 (consBan preuve659 (consBan preuve660 (consBan preuve661 (consBan preuve662 (consBan preuve663 (consBan preuve740 (consBan preuve741 (consBan preuve742 (consBan preuve743 (consBan preuve744 (consBan preuve745 (consBan preuve746 (consBan preuve747 (consBan preuve748 (consBan preuve749 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def fil229 : ℕ := 0x41041041041041003ffff000000000
def etat711 : List ℕ := [fil43,fil44,fil65,fil45,fil46,fil229,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve750 : Ban 60 7 etat711 := viaCut proj22 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def fil230 : ℕ := 0x410410410410410fc0fff000000000
def etat712 : List ℕ := [fil43,fil44,fil65,fil45,fil46,fil230,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve751 : Ban 60 7 etat712 := viaCut proj22 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat713 : List ℕ := [fil43,fil44,fil65,fil45,fil46,fil130,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve752 : Ban 60 7 etat713 := viaCut proj22 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat714 : List ℕ := [fil43,fil44,fil65,fil45,fil46,fil210,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve753 : Ban 60 7 etat714 := viaCut proj22 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def fil231 : ℕ := 0x410410410410410ffffc0000000000
def etat715 : List ℕ := [fil43,fil44,fil65,fil45,fil46,fil231,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve754 : Ban 60 7 etat715 := viaCut proj22 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat716 : List ℕ := [fil43,fil44,fil65,fil45,fil46,fil47,fil150]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve755 : Ban 60 7 etat716 := viaCut proj18 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def etat717 : List ℕ := [fil43,fil44,fil65,fil45,fil46,fil47,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve756 : Ban 60 7 etat717 := viaCut proj19 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def etat718 : List ℕ := [fil43,fil44,fil65,fil45,fil46,fil47,fil124]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve757 : Ban 60 7 etat718 := viaPerm proj24 proj23 preuve329 (by decide +kernel) (by decide +kernel)
def etat719 : List ℕ := [fil43,fil44,fil65,fil45,fil46,fil47,fil125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve758 : Ban 60 7 etat719 := viaPerm proj26 proj26 preuve506 (by decide +kernel) (by decide +kernel)
def etat720 : List ℕ := [fil43,fil44,fil65,fil45,fil46,fil47,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve759 : Ban 60 7 etat720 := viaPerm proj23 proj24 preuve506 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve760 : Ban 60 7 etat397 := viaCut proj20 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat721 : List ℕ := [fil42,fil43,fil44,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve762 : Ban 60 6 etat721 := viaCut proj18 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def etat722 : List ℕ := [fil48,fil43,fil44,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve763 : Ban 60 6 etat722 := viaCut proj18 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def etat723 : List ℕ := [fil49,fil43,fil44,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve764 : Ban 60 6 etat723 := viaCut proj19 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def etat724 : List ℕ := [fil50,fil43,fil44,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve765 : Ban 60 6 etat724 := viaCut proj18 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def etat725 : List ℕ := [fil51,fil43,fil44,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve766 : Ban 60 6 etat725 := viaCut proj19 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def etat726 : List ℕ := [fil52,fil43,fil44,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve767 : Ban 60 6 etat726 := viaCut proj20 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def etat727 : List ℕ := [fil103,fil43,fil44,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve768 : Ban 60 6 etat727 := viaCut proj21 petit7 (by decide) (by decide +kernel) (by decide +kernel)
def etat728 : List ℕ := [fil103,fil43,fil44,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve769 : Ban 60 6 etat728 := viaCut proj21 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def etat729 : List ℕ := [fil53,fil43,fil44,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve770 : Ban 60 6 etat729 := viaCut proj18 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def etat730 : List ℕ := [fil54,fil43,fil44,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve771 : Ban 60 6 etat730 := viaCut proj19 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def etat731 : List ℕ := [fil55,fil43,fil44,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve772 : Ban 60 6 etat731 := viaCut proj20 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def etat732 : List ℕ := [fil104,fil43,fil44,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve773 : Ban 60 6 etat732 := viaCut proj22 petit7 (by decide) (by decide +kernel) (by decide +kernel)
def etat733 : List ℕ := [fil104,fil43,fil44,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve774 : Ban 60 6 etat733 := viaCut proj22 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def etat734 : List ℕ := [fil56,fil43,fil44,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve775 : Ban 60 6 etat734 := viaCut proj21 petit7 (by decide) (by decide +kernel) (by decide +kernel)
def etat735 : List ℕ := [fil57,fil43,fil44,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve776 : Ban 60 6 etat735 := viaCut proj18 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def etat736 : List ℕ := [fil57,fil44,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve777 : Ban 60 6 etat736 := viaCut proj18 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat737 : List ℕ := [fil58,fil43,fil44,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve778 : Ban 60 6 etat737 := viaCut proj18 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def etat738 : List ℕ := [fil58,fil44,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve779 : Ban 60 6 etat738 := viaCut proj18 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat739 : List ℕ := [fil59,fil43,fil44,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve780 : Ban 60 6 etat739 := viaCut proj18 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def etat740 : List ℕ := [fil43,fil61,fil44,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve781 : Ban 60 6 etat740 := viaCut proj19 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def etat741 : List ℕ := [fil43,fil61,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve782 : Ban 60 6 etat741 := viaCut proj19 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat742 : List ℕ := [fil43,fil62,fil44,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve783 : Ban 60 6 etat742 := viaCut proj19 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def etat743 : List ℕ := [fil43,fil62,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve784 : Ban 60 6 etat743 := viaCut proj19 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat744 : List ℕ := [fil43,fil63,fil44,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve785 : Ban 60 6 etat744 := viaCut proj19 petit6 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve786 : Ban 60 6 etat274 := viaCut proj18 petit10 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve787 : Ban 60 6 etat446 := viaCut proj18 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat745 : List ℕ := [fil43,fil44,fil95,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve788 : Ban 60 6 etat745 := viaCut proj20 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def etat746 : List ℕ := [fil43,fil44,fil95,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve789 : Ban 60 6 etat746 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat747 : List ℕ := [fil43,fil44,fil96,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve790 : Ban 60 6 etat747 := viaCut proj20 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def etat748 : List ℕ := [fil43,fil44,fil96,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve791 : Ban 60 6 etat748 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat749 : List ℕ := [fil43,fil44,fil98,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve792 : Ban 60 6 etat749 := viaCut proj20 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def etat750 : List ℕ := [fil43,fil44,fil99,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve793 : Ban 60 6 etat750 := viaCut proj20 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def etat751 : List ℕ := [fil43,fil44,fil45,fil105,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve794 : Ban 60 6 etat751 := viaCut proj19 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat752 : List ℕ := [fil43,fil44,fil45,fil105,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve795 : Ban 60 6 etat752 := viaCut proj20 petit10 (by decide) (by decide +kernel) (by decide +kernel)
def etat753 : List ℕ := [fil43,fil44,fil45,fil100,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve796 : Ban 60 6 etat753 := viaCut proj18 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat754 : List ℕ := [fil43,fil44,fil45,fil106,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve797 : Ban 60 6 etat754 := viaCut proj18 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat755 : List ℕ := [fil43,fil44,fil45,fil106,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve798 : Ban 60 6 etat755 := viaCut proj19 petit12 (by decide) (by decide +kernel) (by decide +kernel)
def etat756 : List ℕ := [fil43,fil44,fil45,fil101,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve799 : Ban 60 6 etat756 := viaCut proj18 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat757 : List ℕ := [fil43,fil44,fil45,fil109,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve800 : Ban 60 6 etat757 := viaCut proj22 petit15 (by decide) (by decide +kernel) (by decide +kernel)
def etat758 : List ℕ := [fil43,fil44,fil45,fil109,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve801 : Ban 60 6 etat758 := viaCut proj18 petit13 (by decide) (by decide +kernel) (by decide +kernel)
def etat759 : List ℕ := [fil43,fil44,fil45,fil110,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve802 : Ban 60 6 etat759 := viaCut proj21 petit15 (by decide) (by decide +kernel) (by decide +kernel)
def etat760 : List ℕ := [fil43,fil44,fil45,fil110,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve803 : Ban 60 6 etat760 := viaCut proj18 petit14 (by decide) (by decide +kernel) (by decide +kernel)
def etat761 : List ℕ := [fil43,fil44,fil45,fil102,fil165,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve804 : Ban 60 6 etat761 := viaCut proj21 petit7 (by decide) (by decide +kernel) (by decide +kernel)
def etat762 : List ℕ := [fil43,fil44,fil45,fil102,fil111,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve805 : Ban 60 6 etat762 := viaCut proj21 petit7 (by decide) (by decide +kernel) (by decide +kernel)
def etat763 : List ℕ := [fil43,fil44,fil45,fil102,fil166,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve806 : Ban 60 6 etat763 := viaCut proj21 petit7 (by decide) (by decide +kernel) (by decide +kernel)
def etat764 : List ℕ := [fil43,fil44,fil45,fil102,fil167,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve807 : Ban 60 6 etat764 := viaCut proj21 petit7 (by decide) (by decide +kernel) (by decide +kernel)
def etat765 : List ℕ := [fil43,fil44,fil45,fil102,fil168,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve808 : Ban 60 6 etat765 := viaCut proj21 petit7 (by decide) (by decide +kernel) (by decide +kernel)
def etat766 : List ℕ := [fil43,fil44,fil45,fil102,fil46,fil164,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve809 : Ban 60 6 etat766 := viaCut proj18 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat767 : List ℕ := [fil43,fil44,fil45,fil102,fil46,fil163,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve810 : Ban 60 6 etat767 := viaCut proj19 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat768 : List ℕ := [fil43,fil44,fil45,fil102,fil46,fil121,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve811 : Ban 60 6 etat768 := viaCut proj21 petit15 (by decide) (by decide +kernel) (by decide +kernel)
def etat769 : List ℕ := [fil43,fil44,fil45,fil102,fil46,fil229,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve812 : Ban 60 6 etat769 := viaCut proj22 petit7 (by decide) (by decide +kernel) (by decide +kernel)
def etat770 : List ℕ := [fil43,fil44,fil45,fil102,fil46,fil122,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve813 : Ban 60 6 etat770 := viaCut proj22 petit7 (by decide) (by decide +kernel) (by decide +kernel)
def etat771 : List ℕ := [fil43,fil44,fil45,fil102,fil46,fil230,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve814 : Ban 60 6 etat771 := viaCut proj22 petit7 (by decide) (by decide +kernel) (by decide +kernel)
def etat772 : List ℕ := [fil43,fil44,fil45,fil102,fil46,fil210,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve815 : Ban 60 6 etat772 := viaCut proj22 petit7 (by decide) (by decide +kernel) (by decide +kernel)
def etat773 : List ℕ := [fil43,fil44,fil45,fil102,fil46,fil231,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve816 : Ban 60 6 etat773 := viaCut proj22 petit7 (by decide) (by decide +kernel) (by decide +kernel)
def etat774 : List ℕ := [fil43,fil44,fil45,fil102,fil46,fil47,fil150]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve817 : Ban 60 6 etat774 := viaCut proj18 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat775 : List ℕ := [fil43,fil44,fil45,fil102,fil46,fil47,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve818 : Ban 60 6 etat775 := viaCut proj19 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat776 : List ℕ := [fil43,fil44,fil45,fil102,fil46,fil47,fil125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve819 : Ban 60 6 etat776 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def etat777 : List ℕ := [fil43,fil44,fil45,fil102,fil46,fil47,fil123]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve820 : Ban 60 6 etat777 := viaCut proj22 petit15 (by decide) (by decide +kernel) (by decide +kernel)
def etat778 : List ℕ := [fil43,fil44,fil45,fil102,fil46,fil47,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve821 : Ban 60 6 etat778 := viaCut proj21 petit15 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve822 : Ban 60 6 etat407 := viaCut proj21 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def etat779 : List ℕ := [fil43,fil44,fil45,fil46,fil122,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve823 : Ban 60 6 etat779 := viaCut proj22 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def etat780 : List ℕ := [fil43,fil44,fil45,fil46,fil47,fil123]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve824 : Ban 60 6 etat780 := viaCut proj22 petit15 (by decide) (by decide +kernel) (by decide +kernel)
def etat781 : List ℕ := [fil43,fil44,fil102,fil46,fil47,fil125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve825 : Ban 60 6 etat781 := viaCut proj22 petit15 (by decide) (by decide +kernel) (by decide +kernel)
def etat782 : List ℕ := [fil43,fil45,fil105,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve826 : Ban 60 6 etat782 := viaCut proj20 petit11 (by decide) (by decide +kernel) (by decide +kernel)
def etat783 : List ℕ := [fil43,fil45,fil102,fil46,fil163,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve827 : Ban 60 6 etat783 := viaCut proj21 petit15 (by decide) (by decide +kernel) (by decide +kernel)
def etat784 : List ℕ := [fil43,fil45,fil102,fil46,fil47,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve828 : Ban 60 6 etat784 := viaCut proj22 petit15 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit86 : Wide 30 5 etat53 := viaSub (ws := [etat53])
  (consBan preuve492 (nilBan _ _))
  (by decide) (by decide +kernel)
def etat785 : List ℕ := [fil44,fil45,fil106,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve829 : Ban 60 6 etat785 := viaCut proj19 petit86 (by decide) (by decide +kernel) (by decide +kernel)
def etat786 : List ℕ := [fil44,fil45,fil102,fil46,fil164,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve830 : Ban 60 6 etat786 := viaCut proj21 petit15 (by decide) (by decide +kernel) (by decide +kernel)
def etat787 : List ℕ := [fil44,fil45,fil102,fil46,fil47,fil150]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve831 : Ban 60 6 etat787 := viaCut proj22 petit15 (by decide) (by decide +kernel) (by decide +kernel)
def etat788 : List ℕ := [fil43,fil44,fil45,fil102,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve761 : Ban 60 7 etat788 := viaBranch (ws := [etat721,etat722,etat723,etat724,etat725,etat726,etat727,etat728,etat729,etat730,etat731,etat732,etat733,etat734,etat735,etat736,etat737,etat738,etat739,etat295,etat740,etat741,etat742,etat743,etat744,etat300,etat305,etat274,etat306,etat446,etat745,etat746,etat747,etat748,etat749,etat750,etat751,etat752,etat753,etat754,etat755,etat756,etat757,etat758,etat759,etat760,etat761,etat762,etat763,etat764,etat765,etat766,etat767,etat592,etat768,etat769,etat770,etat771,etat772,etat773,etat774,etat775,etat776,etat777,etat778,etat407,etat408,etat779,etat780,etat602,etat781,etat782,etat783,etat784,etat785,etat786,etat787])
  (consBan preuve762 (consBan preuve763 (consBan preuve764 (consBan preuve765 (consBan preuve766 (consBan preuve767 (consBan preuve768 (consBan preuve769 (consBan preuve770 (consBan preuve771 (consBan preuve772 (consBan preuve773 (consBan preuve774 (consBan preuve775 (consBan preuve776 (consBan preuve777 (consBan preuve778 (consBan preuve779 (consBan preuve780 (consBan preuve343 (consBan preuve781 (consBan preuve782 (consBan preuve783 (consBan preuve784 (consBan preuve785 (consBan preuve348 (consBan preuve356 (consBan preuve786 (consBan preuve357 (consBan preuve787 (consBan preuve788 (consBan preuve789 (consBan preuve790 (consBan preuve791 (consBan preuve792 (consBan preuve793 (consBan preuve794 (consBan preuve795 (consBan preuve796 (consBan preuve797 (consBan preuve798 (consBan preuve799 (consBan preuve800 (consBan preuve801 (consBan preuve802 (consBan preuve803 (consBan preuve804 (consBan preuve805 (consBan preuve806 (consBan preuve807 (consBan preuve808 (consBan preuve809 (consBan preuve810 (consBan preuve646 (consBan preuve811 (consBan preuve812 (consBan preuve813 (consBan preuve814 (consBan preuve815 (consBan preuve816 (consBan preuve817 (consBan preuve818 (consBan preuve819 (consBan preuve820 (consBan preuve821 (consBan preuve822 (consBan preuve656 (consBan preuve823 (consBan preuve824 (consBan preuve658 (consBan preuve825 (consBan preuve826 (consBan preuve827 (consBan preuve828 (consBan preuve829 (consBan preuve830 (consBan preuve831 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def etat789 : List ℕ := [fil43,fil44,fil45,fil142,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve832 : Ban 60 7 etat789 := viaCut proj21 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat790 : List ℕ := [fil43,fil44,fil45,fil46,fil143,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve833 : Ban 60 7 etat790 := viaPerm proj34 proj34 preuve761 (by decide +kernel) (by decide +kernel)
def etat791 : List ℕ := [fil43,fil44,fil45,fil46,fil130,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve834 : Ban 60 7 etat791 := viaCut proj22 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat792 : List ℕ := [fil43,fil44,fil45,fil46,fil47,fil124]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve835 : Ban 60 7 etat792 := viaPerm proj24 proj23 preuve761 (by decide +kernel) (by decide +kernel)
def etat793 : List ℕ := [fil42,fil43,fil44,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve837 : Ban 60 6 etat793 := viaCut proj18 petit31 (by decide) (by decide +kernel) (by decide +kernel)
def etat794 : List ℕ := [fil48,fil43,fil44,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve838 : Ban 60 6 etat794 := viaCut proj18 petit31 (by decide) (by decide +kernel) (by decide +kernel)
def etat795 : List ℕ := [fil49,fil43,fil44,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve839 : Ban 60 6 etat795 := viaCut proj19 petit31 (by decide) (by decide +kernel) (by decide +kernel)
def etat796 : List ℕ := [fil50,fil43,fil44,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve840 : Ban 60 6 etat796 := viaCut proj18 petit31 (by decide) (by decide +kernel) (by decide +kernel)
def etat797 : List ℕ := [fil51,fil43,fil44,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve841 : Ban 60 6 etat797 := viaCut proj19 petit31 (by decide) (by decide +kernel) (by decide +kernel)
def etat798 : List ℕ := [fil52,fil43,fil44,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve842 : Ban 60 6 etat798 := viaCut proj20 petit17 (by decide) (by decide +kernel) (by decide +kernel)
def etat799 : List ℕ := [fil149,fil43,fil44,fil45,fil46,fil150]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve843 : Ban 60 6 etat799 := viaCut proj18 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def etat800 : List ℕ := [fil149,fil43,fil44,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve844 : Ban 60 6 etat800 := viaCut proj18 petit31 (by decide) (by decide +kernel) (by decide +kernel)
def etat801 : List ℕ := [fil149,fil44,fil45,fil46,fil150]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve845 : Ban 60 6 etat801 := viaCut proj18 petit1 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit87 : Wide 30 5 etat34 := viaSub (ws := [etat0,etat34])
  (consBan preuve93 (consBan preuve71 (nilBan _ _)))
  (by decide) (by decide +kernel)
def etat802 : List ℕ := [fil149,fil44,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve846 : Ban 60 6 etat802 := viaCut proj18 petit87 (by decide) (by decide +kernel) (by decide +kernel)
def etat803 : List ℕ := [fil152,fil43,fil44,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve847 : Ban 60 6 etat803 := viaCut proj19 petit31 (by decide) (by decide +kernel) (by decide +kernel)
def etat804 : List ℕ := [fil152,fil43,fil44,fil45,fil46,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve848 : Ban 60 6 etat804 := viaCut proj19 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def etat805 : List ℕ := [fil152,fil43,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve849 : Ban 60 6 etat805 := viaCut proj19 petit87 (by decide) (by decide +kernel) (by decide +kernel)
def etat806 : List ℕ := [fil152,fil43,fil45,fil46,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve850 : Ban 60 6 etat806 := viaCut proj19 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat807 : List ℕ := [fil155,fil43,fil44,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve851 : Ban 60 6 etat807 := viaCut proj20 petit17 (by decide) (by decide +kernel) (by decide +kernel)
def fil232 : ℕ := 0x3f00000003f000
def etat808 : List ℕ := [fil232,fil43,fil44,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve852 : Ban 60 6 etat808 := viaCut proj20 petit17 (by decide) (by decide +kernel) (by decide +kernel)
def fil233 : ℕ := 0xfc0000000fc0000
def etat809 : List ℕ := [fil233,fil43,fil44,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve853 : Ban 60 6 etat809 := viaCut proj21 petit17 (by decide) (by decide +kernel) (by decide +kernel)
def fil234 : ℕ := 0xfc000003f000000
def etat810 : List ℕ := [fil234,fil43,fil44,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve854 : Ban 60 6 etat810 := viaCut proj21 petit17 (by decide) (by decide +kernel) (by decide +kernel)
def etat811 : List ℕ := [fil202,fil43,fil44,fil45,fil46,fil150]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve855 : Ban 60 6 etat811 := viaCut proj18 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def etat812 : List ℕ := [fil202,fil43,fil44,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve856 : Ban 60 6 etat812 := viaCut proj18 petit31 (by decide) (by decide +kernel) (by decide +kernel)
def etat813 : List ℕ := [fil58,fil43,fil44,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve857 : Ban 60 6 etat813 := viaCut proj18 petit31 (by decide) (by decide +kernel) (by decide +kernel)
def etat814 : List ℕ := [fil58,fil44,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve858 : Ban 60 6 etat814 := viaCut proj18 petit87 (by decide) (by decide +kernel) (by decide +kernel)
def etat815 : List ℕ := [fil59,fil43,fil44,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve859 : Ban 60 6 etat815 := viaCut proj18 petit31 (by decide) (by decide +kernel) (by decide +kernel)
def etat816 : List ℕ := [fil59,fil44,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve860 : Ban 60 6 etat816 := viaCut proj18 petit87 (by decide) (by decide +kernel) (by decide +kernel)
def etat817 : List ℕ := [fil60,fil43,fil44,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve861 : Ban 60 6 etat817 := viaCut proj18 petit31 (by decide) (by decide +kernel) (by decide +kernel)
def etat818 : List ℕ := [fil60,fil44,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve862 : Ban 60 6 etat818 := viaCut proj18 petit87 (by decide) (by decide +kernel) (by decide +kernel)
def fil235 : ℕ := 0x8208208208208200000003f03f000
def etat819 : List ℕ := [fil43,fil235,fil44,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve863 : Ban 60 6 etat819 := viaCut proj19 petit31 (by decide) (by decide +kernel) (by decide +kernel)
def etat820 : List ℕ := [fil43,fil235,fil44,fil45,fil46,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve864 : Ban 60 6 etat820 := viaCut proj19 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def etat821 : List ℕ := [fil43,fil62,fil44,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve865 : Ban 60 6 etat821 := viaCut proj19 petit31 (by decide) (by decide +kernel) (by decide +kernel)
def etat822 : List ℕ := [fil43,fil62,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve866 : Ban 60 6 etat822 := viaCut proj19 petit87 (by decide) (by decide +kernel) (by decide +kernel)
def etat823 : List ℕ := [fil43,fil63,fil44,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve867 : Ban 60 6 etat823 := viaCut proj19 petit31 (by decide) (by decide +kernel) (by decide +kernel)
def etat824 : List ℕ := [fil43,fil63,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve868 : Ban 60 6 etat824 := viaCut proj19 petit87 (by decide) (by decide +kernel) (by decide +kernel)
def etat825 : List ℕ := [fil43,fil64,fil44,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve869 : Ban 60 6 etat825 := viaCut proj19 petit31 (by decide) (by decide +kernel) (by decide +kernel)
def etat826 : List ℕ := [fil43,fil64,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve870 : Ban 60 6 etat826 := viaCut proj18 petit87 (by decide) (by decide +kernel) (by decide +kernel)
def etat827 : List ℕ := [fil43,fil44,fil65,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve871 : Ban 60 6 etat827 := viaCut proj18 petit87 (by decide) (by decide +kernel) (by decide +kernel)
def fil236 : ℕ := 0x104104104104104000000fc0000fc0
def etat828 : List ℕ := [fil43,fil44,fil236,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve872 : Ban 60 6 etat828 := viaCut proj20 petit17 (by decide) (by decide +kernel) (by decide +kernel)
def fil237 : ℕ := 0x104104104104104000000fc003f000
def etat829 : List ℕ := [fil43,fil44,fil237,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve873 : Ban 60 6 etat829 := viaCut proj20 petit17 (by decide) (by decide +kernel) (by decide +kernel)
def etat830 : List ℕ := [fil43,fil44,fil96,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve874 : Ban 60 6 etat830 := viaCut proj20 petit17 (by decide) (by decide +kernel) (by decide +kernel)
def etat831 : List ℕ := [fil43,fil44,fil98,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve875 : Ban 60 6 etat831 := viaCut proj20 petit17 (by decide) (by decide +kernel) (by decide +kernel)
def etat832 : List ℕ := [fil43,fil44,fil99,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve876 : Ban 60 6 etat832 := viaCut proj20 petit17 (by decide) (by decide +kernel) (by decide +kernel)
def etat833 : List ℕ := [fil43,fil44,fil45,fil100,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve877 : Ban 60 6 etat833 := viaCut proj18 petit87 (by decide) (by decide +kernel) (by decide +kernel)
def etat834 : List ℕ := [fil43,fil44,fil45,fil101,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve878 : Ban 60 6 etat834 := viaCut proj19 petit87 (by decide) (by decide +kernel) (by decide +kernel)
def etat835 : List ℕ := [fil43,fil44,fil45,fil204,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve879 : Ban 60 6 etat835 := viaCut proj21 petit17 (by decide) (by decide +kernel) (by decide +kernel)
def fil238 : ℕ := 0x208208208208208000000fff000000
def etat836 : List ℕ := [fil43,fil44,fil45,fil238,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve880 : Ban 60 6 etat836 := viaCut proj21 petit17 (by decide) (by decide +kernel) (by decide +kernel)
def etat837 : List ℕ := [fil43,fil44,fil45,fil166,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve881 : Ban 60 6 etat837 := viaCut proj21 petit17 (by decide) (by decide +kernel) (by decide +kernel)
def etat838 : List ℕ := [fil43,fil44,fil45,fil167,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve882 : Ban 60 6 etat838 := viaCut proj21 petit17 (by decide) (by decide +kernel) (by decide +kernel)
def etat839 : List ℕ := [fil43,fil44,fil45,fil168,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve883 : Ban 60 6 etat839 := viaCut proj21 petit17 (by decide) (by decide +kernel) (by decide +kernel)
def etat840 : List ℕ := [fil43,fil44,fil45,fil46,fil164,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve884 : Ban 60 6 etat840 := viaCut proj18 petit87 (by decide) (by decide +kernel) (by decide +kernel)
def etat841 : List ℕ := [fil43,fil44,fil45,fil46,fil163,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve885 : Ban 60 6 etat841 := viaCut proj19 petit87 (by decide) (by decide +kernel) (by decide +kernel)
def proj55 : Projection 60 60 := pick [32,33,30,31,34,35,8,9,6,7,10,11,20,21,18,19,22,23,14,15,12,13,16,17,26,27,24,25,28,29,2,3,0,1,4,5,50,51,48,49,52,53,56,57,54,55,58,59,38,39,36,37,40,41,44,45,42,43,46,47] rfl (by decide +kernel) (by decide)
def etat842 : List ℕ := [fil43,fil44,fil45,fil46,fil141,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve886 : Ban 60 6 etat842 := viaPerm proj55 proj55 preuve610 (by decide +kernel) (by decide +kernel)
def etat843 : List ℕ := [fil43,fil44,fil45,fil46,fil210,fil150]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve887 : Ban 60 6 etat843 := viaCut proj22 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat844 : List ℕ := [fil43,fil44,fil45,fil46,fil210,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve888 : Ban 60 6 etat844 := viaCut proj22 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat845 : List ℕ := [fil43,fil44,fil45,fil46,fil231,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve889 : Ban 60 6 etat845 := viaCut proj22 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat846 : List ℕ := [fil43,fil44,fil45,fil46,fil231,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve890 : Ban 60 6 etat846 := viaCut proj22 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat847 : List ℕ := [fil43,fil44,fil45,fil46,fil157]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve891 : Ban 60 6 etat847 := viaCut proj18 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat848 : List ℕ := [fil43,fil44,fil45,fil46,fil157,fil150]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve892 : Ban 60 6 etat848 := viaCut proj18 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat849 : List ℕ := [fil43,fil44,fil45,fil46,fil157,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve893 : Ban 60 6 etat849 := viaCut proj18 petit87 (by decide) (by decide +kernel) (by decide +kernel)
def etat850 : List ℕ := [fil43,fil44,fil45,fil46,fil157,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve894 : Ban 60 6 etat850 := viaCut proj19 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat851 : List ℕ := [fil0,fil1,fil2,fil39,fil3,fil20]
def etat852 : List ℕ := [fil0,fil1,fil2,fil39,fil20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve895 : Ban 30 5 etat852 := viaPerm proj12 proj11 preuve289 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve896 : Ban 30 5 etat851 := viaPerm proj12 proj11 preuve229 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit88 : Wide 30 5 etat851 := viaSub (ws := [etat0,etat60,etat852,etat34,etat851])
  (consBan preuve93 (consBan preuve68 (consBan preuve895 (consBan preuve71 (consBan preuve896 (nilBan _ _))))))
  (by decide) (by decide +kernel)
def fil239 : ℕ := 0x45145145145145103ffff000000fff
def etat853 : List ℕ := [fil43,fil44,fil45,fil46,fil239,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve897 : Ban 60 6 etat853 := viaCut proj18 petit88 (by decide) (by decide +kernel) (by decide +kernel)
def fil240 : ℕ := 0x4a5294a41ff801f
def etat854 : List ℕ := [fil0,fil1,fil2,fil3,fil240]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve898 : Ban 30 5 etat854 := viaPerm proj3 proj4 preuve363 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit89 : Wide 30 5 etat854 := viaSub (ws := [etat0,etat854])
  (consBan preuve93 (consBan preuve898 (nilBan _ _)))
  (by decide) (by decide +kernel)
def etat855 : List ℕ := [fil43,fil44,fil45,fil46,fil239,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve899 : Ban 60 6 etat855 := viaCut proj19 petit89 (by decide) (by decide +kernel) (by decide +kernel)
def etat856 : List ℕ := [fil0,fil1,fil2,fil40,fil3,fil20]
def etat857 : List ℕ := [fil0,fil1,fil2,fil40,fil20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve900 : Ban 30 5 etat857 := viaPerm proj15 proj16 preuve289 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve901 : Ban 30 5 etat856 := viaPerm proj15 proj16 preuve229 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit90 : Wide 30 5 etat856 := viaSub (ws := [etat0,etat61,etat857,etat34,etat856])
  (consBan preuve93 (consBan preuve69 (consBan preuve900 (consBan preuve71 (consBan preuve901 (nilBan _ _))))))
  (by decide) (by decide +kernel)
def etat858 : List ℕ := [fil43,fil44,fil45,fil46,fil160,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve902 : Ban 60 6 etat858 := viaCut proj18 petit90 (by decide) (by decide +kernel) (by decide +kernel)
def etat859 : List ℕ := [fil0,fil1,fil2,fil3,fil159]
def proj56 : Projection 30 30 := pick [15,18,17,16,19,5,8,7,6,9,25,28,27,26,29,0,3,2,1,4,20,23,22,21,24,10,13,12,11,14] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve903 : Ban 30 5 etat859 := viaPerm proj56 proj56 preuve363 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit91 : Wide 30 5 etat859 := viaSub (ws := [etat0,etat859])
  (consBan preuve93 (consBan preuve903 (nilBan _ _)))
  (by decide) (by decide +kernel)
def etat860 : List ℕ := [fil43,fil44,fil45,fil46,fil160,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve904 : Ban 60 6 etat860 := viaCut proj19 petit91 (by decide) (by decide +kernel) (by decide +kernel)
def etat861 : List ℕ := [fil43,fil44,fil45,fil46,fil139,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve905 : Ban 60 6 etat861 := viaCut proj19 petit87 (by decide) (by decide +kernel) (by decide +kernel)
def fil241 : ℕ := 0x49249249249249203ffff00003f03f
def etat862 : List ℕ := [fil43,fil44,fil45,fil46,fil150,fil241]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve906 : Ban 60 6 etat862 := viaCut proj18 petit89 (by decide) (by decide +kernel) (by decide +kernel)
def etat863 : List ℕ := [fil43,fil44,fil45,fil46,fil150,fil241,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve907 : Ban 60 6 etat863 := viaCut proj19 petit88 (by decide) (by decide +kernel) (by decide +kernel)
def etat864 : List ℕ := [fil43,fil44,fil45,fil46,fil150,fil212]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve908 : Ban 60 6 etat864 := viaCut proj18 petit91 (by decide) (by decide +kernel) (by decide +kernel)
def etat865 : List ℕ := [fil43,fil44,fil45,fil46,fil150,fil212,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve909 : Ban 60 6 etat865 := viaCut proj19 petit90 (by decide) (by decide +kernel) (by decide +kernel)
def etat866 : List ℕ := [fil43,fil44,fil45,fil46,fil150,fil140,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve910 : Ban 60 6 etat866 := viaCut proj18 petit87 (by decide) (by decide +kernel) (by decide +kernel)
def etat867 : List ℕ := [fil43,fil44,fil45,fil46,fil150,fil153,fil124]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve911 : Ban 60 6 etat867 := viaCut proj18 petit87 (by decide) (by decide +kernel) (by decide +kernel)
def proj57 : Projection 60 60 := pick [1,0,2,3,4,5,13,12,14,15,16,17,7,6,8,9,10,11,25,24,26,27,28,29,19,18,20,21,22,23,31,30,32,33,34,35,43,42,44,45,46,47,37,36,38,39,40,41,49,48,50,51,52,53,55,54,56,57,58,59] rfl (by decide +kernel) (by decide)
def etat868 : List ℕ := [fil43,fil44,fil45,fil46,fil150,fil153,fil195]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve912 : Ban 60 6 etat868 := viaPerm proj57 proj57 preuve473 (by decide +kernel) (by decide +kernel)
def etat869 : List ℕ := [fil43,fil44,fil45,fil46,fil150,fil153,fil196]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve913 : Ban 60 6 etat869 := viaPerm proj34 proj34 preuve473 (by decide +kernel) (by decide +kernel)
def proj58 : Projection 60 60 := pick [1,0,3,2,4,5,25,24,27,26,28,29,19,18,21,20,22,23,13,12,15,14,16,17,7,6,9,8,10,11,31,30,33,32,34,35,43,42,45,44,46,47,37,36,39,38,40,41,55,54,57,56,58,59,49,48,51,50,52,53] rfl (by decide +kernel) (by decide)
def etat870 : List ℕ := [fil43,fil44,fil45,fil46,fil150,fil153,fil194]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve914 : Ban 60 6 etat870 := viaPerm proj58 proj58 preuve473 (by decide +kernel) (by decide +kernel)
def etat871 : List ℕ := [fil43,fil44,fil45,fil46,fil150,fil195]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve915 : Ban 60 6 etat871 := viaCut proj18 petit16 (by decide) (by decide +kernel) (by decide +kernel)
def etat872 : List ℕ := [fil0,fil1,fil2,fil3,fil137]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve916 : Ban 30 5 etat872 := viaPerm proj4 proj3 preuve382 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit92 : Wide 30 5 etat872 := viaSub (ws := [etat0,etat872])
  (consBan preuve93 (consBan preuve916 (nilBan _ _)))
  (by decide) (by decide +kernel)
def etat873 : List ℕ := [fil43,fil44,fil45,fil46,fil150,fil194]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve917 : Ban 60 6 etat873 := viaCut proj18 petit92 (by decide) (by decide +kernel) (by decide +kernel)
def etat874 : List ℕ := [fil43,fil44,fil45,fil46,fil153,fil151]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve918 : Ban 60 6 etat874 := viaCut proj19 petit16 (by decide) (by decide +kernel) (by decide +kernel)
def etat875 : List ℕ := [fil43,fil44,fil45,fil46,fil153,fil196]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve919 : Ban 60 6 etat875 := viaCut proj19 petit92 (by decide) (by decide +kernel) (by decide +kernel)
def etat876 : List ℕ := [fil43,fil65,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve920 : Ban 60 6 etat876 := viaCut proj18 petit87 (by decide) (by decide +kernel) (by decide +kernel)
def proj59 : Projection 60 60 := pick [6,8,9,10,7,11,18,20,21,22,19,23,30,32,33,34,31,35,36,38,39,40,37,41,48,50,51,52,49,53,54,56,57,58,55,59,0,2,3,4,1,5,12,14,15,16,13,17,24,26,27,28,25,29,42,44,45,46,43,47] rfl (by decide +kernel) (by decide)
def proj60 : Projection 60 60 := pick [36,40,37,38,39,41,0,4,1,2,3,5,42,46,43,44,45,47,6,10,7,8,9,11,48,52,49,50,51,53,12,16,13,14,15,17,18,22,19,20,21,23,54,58,55,56,57,59,24,28,25,26,27,29,30,34,31,32,33,35] rfl (by decide +kernel) (by decide)
def etat877 : List ℕ := [fil43,fil45,fil101,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve921 : Ban 60 6 etat877 := viaPerm proj59 proj60 preuve664 (by decide +kernel) (by decide +kernel)
def etat878 : List ℕ := [fil43,fil45,fil46,fil163,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve922 : Ban 60 6 etat878 := viaPerm proj27 proj28 preuve664 (by decide +kernel) (by decide +kernel)
def etat879 : List ℕ := [fil43,fil45,fil46,fil210,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve923 : Ban 60 6 etat879 := viaCut proj22 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat880 : List ℕ := [fil1,fil2,fil19,fil3,fil20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve924 : Ban 30 5 etat880 := viaPerm proj17 proj17 preuve281 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit93 : Wide 30 5 etat880 := viaSub (ws := [etat880])
  (consBan preuve924 (nilBan _ _))
  (by decide) (by decide +kernel)
def etat881 : List ℕ := [fil43,fil45,fil46,fil139,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve925 : Ban 60 6 etat881 := viaCut proj18 petit93 (by decide) (by decide +kernel) (by decide +kernel)
def etat882 : List ℕ := [fil44,fil65,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve926 : Ban 60 6 etat882 := viaCut proj19 petit87 (by decide) (by decide +kernel) (by decide +kernel)
def proj61 : Projection 60 60 := pick [13,14,15,16,12,17,25,26,27,28,24,29,31,32,33,34,30,35,43,44,45,46,42,47,49,50,51,52,48,53,55,56,57,58,54,59,1,2,3,4,0,5,7,8,9,10,6,11,19,20,21,22,18,23,37,38,39,40,36,41] rfl (by decide +kernel) (by decide)
def proj62 : Projection 60 60 := pick [40,36,37,38,39,41,46,42,43,44,45,47,4,0,1,2,3,5,52,48,49,50,51,53,10,6,7,8,9,11,16,12,13,14,15,17,58,54,55,56,57,59,22,18,19,20,21,23,28,24,25,26,27,29,34,30,31,32,33,35] rfl (by decide +kernel) (by decide)
def etat883 : List ℕ := [fil44,fil45,fil100,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve927 : Ban 60 6 etat883 := viaPerm proj61 proj62 preuve664 (by decide +kernel) (by decide +kernel)
def etat884 : List ℕ := [fil44,fil45,fil46,fil164,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve928 : Ban 60 6 etat884 := viaPerm proj30 proj31 preuve664 (by decide +kernel) (by decide +kernel)
def etat885 : List ℕ := [fil44,fil45,fil46,fil231,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve929 : Ban 60 6 etat885 := viaCut proj22 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat886 : List ℕ := [fil44,fil45,fil46,fil150,fil140,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve930 : Ban 60 6 etat886 := viaCut proj19 petit93 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit94 : Wide 30 3 etat368 := viaSearch (by decide +kernel)
def etat887 : List ℕ := [fil42,fil43,fil44,fil141,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve932 : Ban 60 5 etat887 := viaCut proj18 petit94 (by decide) (by decide +kernel) (by decide +kernel)
def etat888 : List ℕ := [fil169,fil43,fil44,fil141,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve933 : Ban 60 5 etat888 := viaCut proj18 petit94 (by decide) (by decide +kernel) (by decide +kernel)
def etat889 : List ℕ := [fil170,fil43,fil44,fil141,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve934 : Ban 60 5 etat889 := viaCut proj19 petit94 (by decide) (by decide +kernel) (by decide +kernel)
def fil242 : ℕ := 0x3f000000fc0
def etat890 : List ℕ := [fil242,fil43,fil44,fil141,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve935 : Ban 60 5 etat890 := viaCut proj18 petit94 (by decide) (by decide +kernel) (by decide +kernel)
def etat891 : List ℕ := [fil197,fil43,fil44,fil141,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve936 : Ban 60 5 etat891 := viaCut proj18 petit94 (by decide) (by decide +kernel) (by decide +kernel)
def fil243 : ℕ := 0xfc000003f000
def etat892 : List ℕ := [fil243,fil43,fil44,fil141,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve937 : Ban 60 5 etat892 := viaCut proj19 petit94 (by decide) (by decide +kernel) (by decide +kernel)
def etat893 : List ℕ := [fil198,fil43,fil44,fil141,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve938 : Ban 60 5 etat893 := viaCut proj19 petit94 (by decide) (by decide +kernel) (by decide +kernel)
def fil244 : ℕ := 0x41041041041041000000000000fff
def etat894 : List ℕ := [fil244,fil43,fil44,fil141,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve939 : Ban 60 5 etat894 := viaCut proj18 petit94 (by decide) (by decide +kernel) (by decide +kernel)
def fil245 : ℕ := 0x41041041041041000000000fc003f
def etat895 : List ℕ := [fil245,fil43,fil44,fil141,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve940 : Ban 60 5 etat895 := viaCut proj18 petit94 (by decide) (by decide +kernel) (by decide +kernel)
def etat896 : List ℕ := [fil174,fil43,fil44,fil141,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve941 : Ban 60 5 etat896 := viaCut proj18 petit94 (by decide) (by decide +kernel) (by decide +kernel)
def etat897 : List ℕ := [fil60,fil43,fil44,fil141,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve942 : Ban 60 5 etat897 := viaCut proj18 petit94 (by decide) (by decide +kernel) (by decide +kernel)
def fil246 : ℕ := 0x8208208208208200000000003f03f
def etat898 : List ℕ := [fil43,fil246,fil44,fil141,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve943 : Ban 60 5 etat898 := viaCut proj19 petit94 (by decide) (by decide +kernel) (by decide +kernel)
def fil247 : ℕ := 0x8208208208208200000003f00003f
def etat899 : List ℕ := [fil43,fil247,fil44,fil141,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve944 : Ban 60 5 etat899 := viaCut proj19 petit94 (by decide) (by decide +kernel) (by decide +kernel)
def etat900 : List ℕ := [fil43,fil175,fil44,fil141,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve945 : Ban 60 5 etat900 := viaCut proj19 petit94 (by decide) (by decide +kernel) (by decide +kernel)
def etat901 : List ℕ := [fil43,fil64,fil44,fil141,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve946 : Ban 60 5 etat901 := viaCut proj19 petit94 (by decide) (by decide +kernel) (by decide +kernel)
def fil248 : ℕ := 0x10410410410410400000000003ffc0
def etat902 : List ℕ := [fil43,fil44,fil248,fil141,fil125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve947 : Ban 60 5 etat902 := viaCut proj20 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def etat903 : List ℕ := [fil43,fil44,fil248,fil141,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve948 : Ban 60 5 etat903 := viaCut proj20 petit44 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit95 : Wide 30 5 etat64 := viaSub (ws := [etat0,etat64])
  (consBan preuve93 (consBan preuve73 (nilBan _ _)))
  (by decide) (by decide +kernel)
def fil249 : ℕ := 0x104104104104104fff000fc003ffc0
def etat904 : List ℕ := [fil43,fil44,fil249,fil141,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve949 : Ban 60 5 etat904 := viaCut proj21 petit95 (by decide) (by decide +kernel) (by decide +kernel)
def etat905 : List ℕ := [fil43,fil44,fil249,fil141,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve950 : Ban 60 5 etat905 := viaCut proj21 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat906 : List ℕ := [fil43,fil44,fil249,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve951 : Ban 60 5 etat906 := viaCut proj22 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat907 : List ℕ := [fil43,fil44,fil249,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve952 : Ban 60 5 etat907 := viaCut proj21 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def fil250 : ℕ := 0x20820820820820800000003ffc0000
def etat908 : List ℕ := [fil43,fil44,fil250,fil141,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve953 : Ban 60 5 etat908 := viaCut proj21 petit44 (by decide) (by decide +kernel) (by decide +kernel)
def etat909 : List ℕ := [fil43,fil44,fil250,fil141,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve954 : Ban 60 5 etat909 := viaCut proj21 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def fil251 : ℕ := 0x208208208208208fff000ffffc0000
def etat910 : List ℕ := [fil43,fil44,fil251,fil141,fil125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve955 : Ban 60 5 etat910 := viaCut proj20 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat911 : List ℕ := [fil43,fil44,fil251,fil141,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve956 : Ban 60 5 etat911 := viaCut proj20 petit95 (by decide) (by decide +kernel) (by decide +kernel)
def etat912 : List ℕ := [fil43,fil44,fil251,fil125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve957 : Ban 60 5 etat912 := viaCut proj20 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat913 : List ℕ := [fil43,fil44,fil251,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve958 : Ban 60 5 etat913 := viaCut proj22 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat914 : List ℕ := [fil43,fil44,fil179,fil141,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve959 : Ban 60 5 etat914 := viaCut proj19 petit50 (by decide) (by decide +kernel) (by decide +kernel)
def etat915 : List ℕ := [fil0,fil1,fil2,fil3,fil213]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve960 : Ban 30 5 etat915 := viaPerm proj7 proj7 preuve363 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit96 : Wide 30 5 etat915 := viaSub (ws := [etat0,etat915])
  (consBan preuve93 (consBan preuve960 (nilBan _ _)))
  (by decide) (by decide +kernel)
def etat916 : List ℕ := [fil43,fil44,fil179,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve961 : Ban 60 5 etat916 := viaCut proj22 petit96 (by decide) (by decide +kernel) (by decide +kernel)
def etat917 : List ℕ := [fil43,fil44,fil180,fil141,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve962 : Ban 60 5 etat917 := viaCut proj18 petit50 (by decide) (by decide +kernel) (by decide +kernel)
def etat918 : List ℕ := [fil0,fil1,fil2,fil3,fil136]
def proj63 : Projection 30 30 := pick [27,28,26,25,29,12,13,11,10,14,22,23,21,20,24,7,8,6,5,9,17,18,16,15,19,2,3,1,0,4] rfl (by decide +kernel) (by decide)
def proj64 : Projection 30 30 := pick [28,27,25,26,29,18,17,15,16,19,8,7,5,6,9,23,22,20,21,24,13,12,10,11,14,3,2,0,1,4] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve963 : Ban 30 5 etat918 := viaPerm proj63 proj64 preuve363 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit97 : Wide 30 5 etat918 := viaSub (ws := [etat0,etat918])
  (consBan preuve93 (consBan preuve963 (nilBan _ _)))
  (by decide) (by decide +kernel)
def etat919 : List ℕ := [fil43,fil44,fil180,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve964 : Ban 60 5 etat919 := viaCut proj22 petit97 (by decide) (by decide +kernel) (by decide +kernel)
def etat920 : List ℕ := [fil43,fil44,fil141,fil181,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve965 : Ban 60 5 etat920 := viaCut proj18 petit50 (by decide) (by decide +kernel) (by decide +kernel)
def etat921 : List ℕ := [fil43,fil44,fil141,fil182,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve966 : Ban 60 5 etat921 := viaCut proj19 petit50 (by decide) (by decide +kernel) (by decide +kernel)
def etat922 : List ℕ := [fil43,fil44,fil141,fil183,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve967 : Ban 60 5 etat922 := viaCut proj22 petit44 (by decide) (by decide +kernel) (by decide +kernel)
def etat923 : List ℕ := [fil43,fil44,fil141,fil189]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve968 : Ban 60 5 etat923 := viaCut proj20 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat924 : List ℕ := [fil43,fil44,fil141,fil189,fil125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve969 : Ban 60 5 etat924 := viaCut proj20 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat925 : List ℕ := [fil43,fil44,fil141,fil189,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve970 : Ban 60 5 etat925 := viaCut proj20 petit95 (by decide) (by decide +kernel) (by decide +kernel)
def etat926 : List ℕ := [fil43,fil44,fil141,fil189,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve971 : Ban 60 5 etat926 := viaCut proj21 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def fil252 : ℕ := 0x514514514514514fff03ffc0000fc0
def etat927 : List ℕ := [fil43,fil44,fil141,fil252,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve972 : Ban 60 5 etat927 := viaCut proj19 petit50 (by decide) (by decide +kernel) (by decide +kernel)
def etat928 : List ℕ := [fil43,fil44,fil141,fil252,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve973 : Ban 60 5 etat928 := viaCut proj21 petit96 (by decide) (by decide +kernel) (by decide +kernel)
def etat929 : List ℕ := [fil43,fil44,fil141,fil162,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve974 : Ban 60 5 etat929 := viaCut proj18 petit50 (by decide) (by decide +kernel) (by decide +kernel)
def etat930 : List ℕ := [fil43,fil44,fil141,fil162,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve975 : Ban 60 5 etat930 := viaCut proj21 petit97 (by decide) (by decide +kernel) (by decide +kernel)
def etat931 : List ℕ := [fil43,fil44,fil141,fil125,fil151,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve976 : Ban 60 5 etat931 := viaCut proj18 petit50 (by decide) (by decide +kernel) (by decide +kernel)
def etat932 : List ℕ := [fil43,fil44,fil141,fil125,fil195,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve977 : Ban 60 5 etat932 := viaCut proj19 petit50 (by decide) (by decide +kernel) (by decide +kernel)
def etat933 : List ℕ := [fil43,fil44,fil141,fil125,fil218]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve978 : Ban 60 5 etat933 := viaCut proj20 petit96 (by decide) (by decide +kernel) (by decide +kernel)
def etat934 : List ℕ := [fil43,fil44,fil141,fil125,fil218,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve979 : Ban 60 5 etat934 := viaCut proj19 petit50 (by decide) (by decide +kernel) (by decide +kernel)
def etat935 : List ℕ := [fil43,fil44,fil141,fil125,fil219]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve980 : Ban 60 5 etat935 := viaCut proj20 petit97 (by decide) (by decide +kernel) (by decide +kernel)
def etat936 : List ℕ := [fil43,fil44,fil141,fil125,fil219,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve981 : Ban 60 5 etat936 := viaCut proj18 petit50 (by decide) (by decide +kernel) (by decide +kernel)
def etat937 : List ℕ := [fil43,fil44,fil141,fil125,fil186,fil196]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve982 : Ban 60 5 etat937 := viaCut proj18 petit50 (by decide) (by decide +kernel) (by decide +kernel)
def etat938 : List ℕ := [fil43,fil44,fil141,fil125,fil186,fil194]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve983 : Ban 60 5 etat938 := viaCut proj19 petit50 (by decide) (by decide +kernel) (by decide +kernel)
def etat939 : List ℕ := [fil43,fil44,fil141,fil125,fil186,fil185]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve984 : Ban 60 5 etat939 := viaCut proj20 petit95 (by decide) (by decide +kernel) (by decide +kernel)
def etat940 : List ℕ := [fil43,fil44,fil141,fil125,fil196]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve985 : Ban 60 5 etat940 := viaCut proj20 petit92 (by decide) (by decide +kernel) (by decide +kernel)
def etat941 : List ℕ := [fil43,fil44,fil141,fil125,fil194]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve986 : Ban 60 5 etat941 := viaCut proj20 petit48 (by decide) (by decide +kernel) (by decide +kernel)
def etat942 : List ℕ := [fil43,fil44,fil141,fil151,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve987 : Ban 60 5 etat942 := viaCut proj21 petit92 (by decide) (by decide +kernel) (by decide +kernel)
def etat943 : List ℕ := [fil43,fil44,fil141,fil195,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve988 : Ban 60 5 etat943 := viaCut proj21 petit48 (by decide) (by decide +kernel) (by decide +kernel)
def etat944 : List ℕ := [fil43,fil44,fil181,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve989 : Ban 60 5 etat944 := viaCut proj22 petit92 (by decide) (by decide +kernel) (by decide +kernel)
def etat945 : List ℕ := [fil43,fil44,fil182,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve990 : Ban 60 5 etat945 := viaCut proj22 petit48 (by decide) (by decide +kernel) (by decide +kernel)
def etat946 : List ℕ := [fil43,fil44,fil183,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve991 : Ban 60 5 etat946 := viaCut proj22 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def etat947 : List ℕ := [fil43,fil44,fil141,fil125,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve931 : Ban 60 6 etat947 := viaBranch (ws := [etat887,etat888,etat889,etat890,etat891,etat892,etat893,etat894,etat895,etat896,etat897,etat898,etat899,etat900,etat901,etat555,etat902,etat903,etat904,etat905,etat906,etat907,etat908,etat909,etat910,etat911,etat912,etat913,etat914,etat916,etat917,etat919,etat920,etat921,etat922,etat923,etat924,etat925,etat926,etat927,etat928,etat929,etat930,etat931,etat932,etat933,etat934,etat935,etat936,etat937,etat938,etat939,etat940,etat941,etat942,etat943,etat944,etat945,etat946])
  (consBan preuve932 (consBan preuve933 (consBan preuve934 (consBan preuve935 (consBan preuve936 (consBan preuve937 (consBan preuve938 (consBan preuve939 (consBan preuve940 (consBan preuve941 (consBan preuve942 (consBan preuve943 (consBan preuve944 (consBan preuve945 (consBan preuve946 (consBan preuve615 (consBan preuve947 (consBan preuve948 (consBan preuve949 (consBan preuve950 (consBan preuve951 (consBan preuve952 (consBan preuve953 (consBan preuve954 (consBan preuve955 (consBan preuve956 (consBan preuve957 (consBan preuve958 (consBan preuve959 (consBan preuve961 (consBan preuve962 (consBan preuve964 (consBan preuve965 (consBan preuve966 (consBan preuve967 (consBan preuve968 (consBan preuve969 (consBan preuve970 (consBan preuve971 (consBan preuve972 (consBan preuve973 (consBan preuve974 (consBan preuve975 (consBan preuve976 (consBan preuve977 (consBan preuve978 (consBan preuve979 (consBan preuve980 (consBan preuve981 (consBan preuve982 (consBan preuve983 (consBan preuve984 (consBan preuve985 (consBan preuve986 (consBan preuve987 (consBan preuve988 (consBan preuve989 (consBan preuve990 (consBan preuve991 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def etat948 : List ℕ := [fil65,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve992 : Ban 60 6 etat948 := viaPerm proj55 proj55 preuve931 (by decide +kernel) (by decide +kernel)
def etat949 : List ℕ := [fil43,fil44,fil45,fil46,fil150,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve836 : Ban 60 7 etat949 := viaBranch (ws := [etat793,etat794,etat795,etat796,etat797,etat798,etat799,etat800,etat801,etat802,etat803,etat804,etat805,etat806,etat807,etat808,etat809,etat810,etat811,etat812,etat813,etat814,etat815,etat816,etat817,etat818,etat819,etat820,etat821,etat822,etat823,etat824,etat825,etat826,etat827,etat828,etat829,etat830,etat831,etat832,etat833,etat834,etat835,etat836,etat837,etat838,etat839,etat840,etat841,etat842,etat843,etat844,etat845,etat846,etat847,etat848,etat849,etat850,etat853,etat855,etat858,etat860,etat861,etat862,etat863,etat864,etat865,etat866,etat867,etat436,etat868,etat869,etat870,etat871,etat873,etat874,etat875,etat876,etat877,etat878,etat879,etat881,etat882,etat883,etat884,etat885,etat886,etat948])
  (consBan preuve837 (consBan preuve838 (consBan preuve839 (consBan preuve840 (consBan preuve841 (consBan preuve842 (consBan preuve843 (consBan preuve844 (consBan preuve845 (consBan preuve846 (consBan preuve847 (consBan preuve848 (consBan preuve849 (consBan preuve850 (consBan preuve851 (consBan preuve852 (consBan preuve853 (consBan preuve854 (consBan preuve855 (consBan preuve856 (consBan preuve857 (consBan preuve858 (consBan preuve859 (consBan preuve860 (consBan preuve861 (consBan preuve862 (consBan preuve863 (consBan preuve864 (consBan preuve865 (consBan preuve866 (consBan preuve867 (consBan preuve868 (consBan preuve869 (consBan preuve870 (consBan preuve871 (consBan preuve872 (consBan preuve873 (consBan preuve874 (consBan preuve875 (consBan preuve876 (consBan preuve877 (consBan preuve878 (consBan preuve879 (consBan preuve880 (consBan preuve881 (consBan preuve882 (consBan preuve883 (consBan preuve884 (consBan preuve885 (consBan preuve886 (consBan preuve887 (consBan preuve888 (consBan preuve889 (consBan preuve890 (consBan preuve891 (consBan preuve892 (consBan preuve893 (consBan preuve894 (consBan preuve897 (consBan preuve899 (consBan preuve902 (consBan preuve904 (consBan preuve905 (consBan preuve906 (consBan preuve907 (consBan preuve908 (consBan preuve909 (consBan preuve910 (consBan preuve911 (consBan preuve473 (consBan preuve912 (consBan preuve913 (consBan preuve914 (consBan preuve915 (consBan preuve917 (consBan preuve918 (consBan preuve919 (consBan preuve920 (consBan preuve921 (consBan preuve922 (consBan preuve923 (consBan preuve925 (consBan preuve926 (consBan preuve927 (consBan preuve928 (consBan preuve929 (consBan preuve930 (consBan preuve992 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def etat950 : List ℕ := [fil43,fil65,fil45,fil101,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve993 : Ban 60 7 etat950 := viaPerm proj59 proj60 preuve836 (by decide +kernel) (by decide +kernel)
def etat951 : List ℕ := [fil43,fil65,fil45,fil46,fil163,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve994 : Ban 60 7 etat951 := viaPerm proj27 proj28 preuve836 (by decide +kernel) (by decide +kernel)
def etat952 : List ℕ := [fil43,fil65,fil45,fil46,fil47,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve995 : Ban 60 7 etat952 := viaPerm proj29 proj29 preuve836 (by decide +kernel) (by decide +kernel)
def etat953 : List ℕ := [fil64,fil44,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve996 : Ban 60 7 etat953 := viaCut proj19 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def etat954 : List ℕ := [fil44,fil65,fil45,fil100,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve997 : Ban 60 7 etat954 := viaPerm proj61 proj62 preuve836 (by decide +kernel) (by decide +kernel)
def etat955 : List ℕ := [fil44,fil65,fil45,fil46,fil164,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve998 : Ban 60 7 etat955 := viaPerm proj30 proj31 preuve836 (by decide +kernel) (by decide +kernel)
def etat956 : List ℕ := [fil44,fil65,fil45,fil46,fil47,fil150]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve999 : Ban 60 7 etat956 := viaPerm proj32 proj33 preuve836 (by decide +kernel) (by decide +kernel)
def etat957 : List ℕ := [fil43,fil44,fil65,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve92 : Ban 60 8 etat957 := viaBranch (ws := [etat83,etat84,etat85,etat86,etat87,etat88,etat89,etat90,etat91,etat92,etat93,etat94,etat95,etat96,etat97,etat98,etat99,etat100,etat101,etat102,etat103,etat104,etat105,etat106,etat107,etat108,etat78,etat109,etat110,etat111,etat112,etat113,etat114,etat115,etat116,etat82,etat269,etat270,etat271,etat272,etat273,etat274,etat275,etat276,etat277,etat278,etat279,etat280,etat281,etat446,etat447,etat448,etat449,etat450,etat451,etat452,etat453,etat454,etat710,etat711,etat712,etat713,etat714,etat715,etat716,etat717,etat718,etat719,etat720,etat397,etat788,etat789,etat790,etat791,etat792,etat950,etat951,etat952,etat953,etat954,etat955,etat956])
  (consBan preuve111 (consBan preuve112 (consBan preuve113 (consBan preuve114 (consBan preuve115 (consBan preuve116 (consBan preuve117 (consBan preuve118 (consBan preuve119 (consBan preuve120 (consBan preuve121 (consBan preuve122 (consBan preuve123 (consBan preuve124 (consBan preuve125 (consBan preuve126 (consBan preuve127 (consBan preuve128 (consBan preuve129 (consBan preuve130 (consBan preuve131 (consBan preuve132 (consBan preuve133 (consBan preuve134 (consBan preuve135 (consBan preuve136 (consBan preuve137 (consBan preuve138 (consBan preuve139 (consBan preuve140 (consBan preuve141 (consBan preuve142 (consBan preuve143 (consBan preuve144 (consBan preuve145 (consBan preuve146 (consBan preuve314 (consBan preuve315 (consBan preuve317 (consBan preuve318 (consBan preuve320 (consBan preuve321 (consBan preuve322 (consBan preuve323 (consBan preuve324 (consBan preuve325 (consBan preuve326 (consBan preuve327 (consBan preuve328 (consBan preuve329 (consBan preuve498 (consBan preuve499 (consBan preuve500 (consBan preuve501 (consBan preuve502 (consBan preuve503 (consBan preuve504 (consBan preuve505 (consBan preuve506 (consBan preuve750 (consBan preuve751 (consBan preuve752 (consBan preuve753 (consBan preuve754 (consBan preuve755 (consBan preuve756 (consBan preuve757 (consBan preuve758 (consBan preuve759 (consBan preuve760 (consBan preuve761 (consBan preuve832 (consBan preuve833 (consBan preuve834 (consBan preuve835 (consBan preuve993 (consBan preuve994 (consBan preuve995 (consBan preuve996 (consBan preuve997 (consBan preuve998 (consBan preuve999 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def etat958 : List ℕ := [fil43,fil44,fil95,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1000 : Ban 60 8 etat958 := viaCut proj20 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def etat959 : List ℕ := [fil43,fil44,fil96,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1001 : Ban 60 8 etat959 := viaCut proj20 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def etat960 : List ℕ := [fil43,fil44,fil98,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1002 : Ban 60 8 etat960 := viaCut proj20 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def etat961 : List ℕ := [fil43,fil44,fil99,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1003 : Ban 60 8 etat961 := viaCut proj20 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def proj65 : Projection 60 60 := pick [6,8,7,9,10,11,0,2,1,3,4,5,12,14,13,15,16,17,18,20,19,21,22,23,30,32,31,33,34,35,24,26,25,27,28,29,36,38,37,39,40,41,48,50,49,51,52,53,42,44,43,45,46,47,54,56,55,57,58,59] rfl (by decide +kernel) (by decide)
def etat962 : List ℕ := [fil43,fil44,fil45,fil100,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1004 : Ban 60 8 etat962 := viaPerm proj65 proj65 preuve92 (by decide +kernel) (by decide +kernel)
def etat963 : List ℕ := [fil43,fil44,fil45,fil101,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1005 : Ban 60 8 etat963 := viaPerm proj49 proj48 preuve92 (by decide +kernel) (by decide +kernel)
def etat964 : List ℕ := [fil43,fil44,fil45,fil165,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1006 : Ban 60 8 etat964 := viaCut proj21 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def etat965 : List ℕ := [fil43,fil44,fil45,fil166,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1007 : Ban 60 8 etat965 := viaCut proj21 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def etat966 : List ℕ := [fil43,fil44,fil45,fil167,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1008 : Ban 60 8 etat966 := viaCut proj21 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def etat967 : List ℕ := [fil43,fil44,fil45,fil168,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1009 : Ban 60 8 etat967 := viaCut proj21 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def etat968 : List ℕ := [fil43,fil44,fil45,fil46,fil164,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1010 : Ban 60 8 etat968 := viaPerm proj45 proj44 preuve92 (by decide +kernel) (by decide +kernel)
def proj66 : Projection 60 60 := pick [25,27,24,26,28,29,1,3,0,2,4,5,19,21,18,20,22,23,13,15,12,14,16,17,31,33,30,32,34,35,7,9,6,8,10,11,43,45,42,44,46,47,55,57,54,56,58,59,37,39,36,38,40,41,49,51,48,50,52,53] rfl (by decide +kernel) (by decide)
def proj67 : Projection 60 60 := pick [8,6,9,7,10,11,32,30,33,31,34,35,20,18,21,19,22,23,14,12,15,13,16,17,2,0,3,1,4,5,26,24,27,25,28,29,50,48,51,49,52,53,38,36,39,37,40,41,56,54,57,55,58,59,44,42,45,43,46,47] rfl (by decide +kernel) (by decide)
def etat969 : List ℕ := [fil43,fil44,fil45,fil46,fil163,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1011 : Ban 60 8 etat969 := viaPerm proj66 proj67 preuve92 (by decide +kernel) (by decide +kernel)
def etat970 : List ℕ := [fil43,fil44,fil45,fil46,fil141,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1012 : Ban 60 8 etat970 := viaPerm proj55 proj55 preuve92 (by decide +kernel) (by decide +kernel)
def etat971 : List ℕ := [fil43,fil44,fil45,fil46,fil229,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1013 : Ban 60 8 etat971 := viaCut proj22 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def etat972 : List ℕ := [fil43,fil44,fil45,fil46,fil230,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1014 : Ban 60 8 etat972 := viaCut proj22 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def etat973 : List ℕ := [fil43,fil44,fil45,fil46,fil210,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1015 : Ban 60 8 etat973 := viaCut proj22 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def etat974 : List ℕ := [fil43,fil44,fil45,fil46,fil231,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1016 : Ban 60 8 etat974 := viaCut proj22 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def etat975 : List ℕ := [fil43,fil44,fil45,fil46,fil47,fil150]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1017 : Ban 60 8 etat975 := viaPerm proj60 proj59 preuve92 (by decide +kernel) (by decide +kernel)
def proj68 : Projection 60 60 := pick [43,46,42,44,45,47,1,4,0,2,3,5,37,40,36,38,39,41,13,16,12,14,15,17,49,52,48,50,51,53,7,10,6,8,9,11,25,28,24,26,27,29,55,58,54,56,57,59,19,22,18,20,21,23,31,34,30,32,33,35] rfl (by decide +kernel) (by decide)
def proj69 : Projection 60 60 := pick [8,6,9,10,7,11,32,30,33,34,31,35,20,18,21,22,19,23,50,48,51,52,49,53,38,36,39,40,37,41,56,54,57,58,55,59,14,12,15,16,13,17,2,0,3,4,1,5,26,24,27,28,25,29,44,42,45,46,43,47] rfl (by decide +kernel) (by decide)
def etat976 : List ℕ := [fil43,fil44,fil45,fil46,fil47,fil153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1018 : Ban 60 8 etat976 := viaPerm proj68 proj69 preuve92 (by decide +kernel) (by decide +kernel)
def etat977 : List ℕ := [fil43,fil44,fil45,fil46,fil47,fil125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1019 : Ban 60 8 etat977 := viaPerm proj43 proj42 preuve92 (by decide +kernel) (by decide +kernel)
def proj70 : Projection 60 60 := pick [57,58,54,55,56,59,21,22,18,19,20,23,39,40,36,37,38,41,27,28,24,25,26,29,45,46,42,43,44,47,3,4,0,1,2,5,33,34,30,31,32,35,51,52,48,49,50,53,9,10,6,7,8,11,15,16,12,13,14,17] rfl (by decide +kernel) (by decide)
def proj71 : Projection 60 60 := pick [32,33,34,30,31,35,50,51,52,48,49,53,56,57,58,54,55,59,8,9,10,6,7,11,20,21,22,18,19,23,38,39,40,36,37,41,14,15,16,12,13,17,26,27,28,24,25,29,44,45,46,42,43,47,2,3,4,0,1,5] rfl (by decide +kernel) (by decide)
def etat978 : List ℕ := [fil43,fil44,fil45,fil46,fil47,fil186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1020 : Ban 60 8 etat978 := viaPerm proj70 proj71 preuve92 (by decide +kernel) (by decide +kernel)
def etat979 : List ℕ := [fil43,fil44,fil45,fil46,fil47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1 : Ban 60 9 etat979 := viaBranch (ws := [etat65,etat66,etat67,etat68,etat69,etat70,etat71,etat72,etat73,etat74,etat75,etat76,etat77,etat78,etat79,etat80,etat81,etat82,etat957,etat958,etat959,etat960,etat961,etat962,etat963,etat964,etat965,etat966,etat967,etat968,etat969,etat970,etat971,etat972,etat973,etat974,etat975,etat976,etat977,etat978])
  (consBan preuve74 (consBan preuve75 (consBan preuve76 (consBan preuve77 (consBan preuve78 (consBan preuve79 (consBan preuve80 (consBan preuve81 (consBan preuve82 (consBan preuve83 (consBan preuve84 (consBan preuve85 (consBan preuve86 (consBan preuve87 (consBan preuve88 (consBan preuve89 (consBan preuve90 (consBan preuve91 (consBan preuve92 (consBan preuve1000 (consBan preuve1001 (consBan preuve1002 (consBan preuve1003 (consBan preuve1004 (consBan preuve1005 (consBan preuve1006 (consBan preuve1007 (consBan preuve1008 (consBan preuve1009 (consBan preuve1010 (consBan preuve1011 (consBan preuve1012 (consBan preuve1013 (consBan preuve1014 (consBan preuve1015 (consBan preuve1016 (consBan preuve1017 (consBan preuve1018 (consBan preuve1019 (consBan preuve1020 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem cinq : Wide 60 9 etat979 := widen (by decide +kernel) preuve1
def fil253 : ℕ := 0x7f
def fil254 : ℕ := 0x81020408102040810204081020000001fc00001fc000fe03fff
def fil255 : ℕ := 0x1020408102040810204081020400000fe00000fe0007f01fc07f
def fil256 : ℕ := 0x204081020408102040810204080007f000007f0003f8001fff80
def fil257 : ℕ := 0x4081020408102040810204081003f800003f800003ffffe00000
def fil258 : ℕ := 0x81020408102040810204081021fc0000003ffffffc0000000000
def fil259 : ℕ := 0x102040810204081020408102041ffffffffc00000000000000000
def etat980 : List ℕ := [fil253,fil254,fil255,fil256,fil257,fil258,fil259]
def proj72 : Projection 105 60 := pick [15,16,17,18,19,20,29,30,31,32,33,34,36,37,38,39,40,41,50,51,52,53,54,55,57,58,59,60,61,62,64,65,66,67,68,69,78,79,80,81,82,83,85,86,87,88,89,90,92,93,94,95,96,97,99,100,101,102,103,104] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1022 : Ban 105 10 etat980 := viaCut proj72 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil260 : ℕ := 0x3f80
def etat981 : List ℕ := [fil260,fil254,fil255,fil256,fil257,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1023 : Ban 105 10 etat981 := viaCut proj72 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil261 : ℕ := 0x1fc000
def etat982 : List ℕ := [fil261,fil254,fil255,fil256,fil257,fil258,fil259]
def proj73 : Projection 105 60 := pick [7,9,10,11,12,13,21,23,24,25,26,27,35,37,38,39,40,41,42,44,45,46,47,48,56,58,59,60,61,62,63,65,66,67,68,69,70,72,73,74,75,76,84,86,87,88,89,90,91,93,94,95,96,97,98,100,101,102,103,104] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1024 : Ban 105 10 etat982 := viaCut proj73 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil262 : ℕ := 0xfe00000
def etat983 : List ℕ := [fil262,fil254,fil255,fil256,fil257,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1025 : Ban 105 10 etat983 := viaCut proj72 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil263 : ℕ := 0x7f0000000
def etat984 : List ℕ := [fil263,fil254,fil255,fil256,fil257,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1026 : Ban 105 10 etat984 := viaCut proj73 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil264 : ℕ := 0x3f800000000
def etat985 : List ℕ := [fil264,fil254,fil255,fil256,fil257,fil258,fil259]
def proj74 : Projection 105 60 := pick [0,1,3,4,5,6,21,22,24,25,26,27,28,29,31,32,33,34,42,43,45,46,47,48,49,50,52,53,54,55,63,64,66,67,68,69,70,71,73,74,75,76,77,78,80,81,82,83,91,92,94,95,96,97,98,99,101,102,103,104] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1027 : Ban 105 10 etat985 := viaCut proj74 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil265 : ℕ := 0x1fc0000000000
def etat986 : List ℕ := [fil265,fil254,fil255,fil256,fil257,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1028 : Ban 105 10 etat986 := viaCut proj72 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil266 : ℕ := 0xfe000000000000
def etat987 : List ℕ := [fil266,fil254,fil255,fil256,fil257,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1029 : Ban 105 10 etat987 := viaCut proj73 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil267 : ℕ := 0x7f00000000000000
def etat988 : List ℕ := [fil267,fil254,fil255,fil256,fil257,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1030 : Ban 105 10 etat988 := viaCut proj74 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil268 : ℕ := 0x3f8000000000000000
def etat989 : List ℕ := [fil268,fil254,fil255,fil256,fil257,fil258,fil259]
def proj75 : Projection 105 60 := pick [0,1,2,4,5,6,7,8,9,11,12,13,14,15,16,18,19,20,42,43,44,46,47,48,49,50,51,53,54,55,56,57,58,60,61,62,70,71,72,74,75,76,77,78,79,81,82,83,84,85,86,88,89,90,98,99,100,102,103,104] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1031 : Ban 105 10 etat989 := viaCut proj75 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil269 : ℕ := 0x1fc00000000000000000
def etat990 : List ℕ := [fil269,fil254,fil255,fil256,fil257,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1032 : Ban 105 10 etat990 := viaCut proj72 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil270 : ℕ := 0xfe0000000000000000000
def etat991 : List ℕ := [fil270,fil254,fil255,fil256,fil257,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1033 : Ban 105 10 etat991 := viaCut proj73 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil271 : ℕ := 0x7f000000000000000000000
def etat992 : List ℕ := [fil271,fil254,fil255,fil256,fil257,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1034 : Ban 105 10 etat992 := viaCut proj74 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil272 : ℕ := 0x3f80000000000000000000000
def etat993 : List ℕ := [fil272,fil254,fil255,fil256,fil257,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1035 : Ban 105 10 etat993 := viaCut proj75 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil273 : ℕ := 0x1fc000000000000000000000000
def etat994 : List ℕ := [fil273,fil254,fil255,fil256,fil257,fil258,fil259]
def proj76 : Projection 105 60 := pick [0,1,2,3,5,6,7,8,9,10,12,13,14,15,16,17,19,20,21,22,23,24,26,27,28,29,30,31,33,34,35,36,37,38,40,41,70,71,72,73,75,76,77,78,79,80,82,83,84,85,86,87,89,90,91,92,93,94,96,97] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1036 : Ban 105 10 etat994 := viaCut proj76 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil274 : ℕ := 0x810204081020408102040810200000000000001fc000fe03fff
def etat995 : List ℕ := [fil274,fil254,fil255,fil256,fil257,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1037 : Ban 105 10 etat995 := viaCut proj72 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil275 : ℕ := 0x81020408102040810204081020000001fc0000000000fe03fff
def etat996 : List ℕ := [fil275,fil254,fil255,fil256,fil257,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1038 : Ban 105 10 etat996 := viaCut proj72 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil276 : ℕ := 0x81020408102040810204081020000001fc00001fc0000003fff
def etat997 : List ℕ := [fil276,fil254,fil255,fil256,fil257,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1039 : Ban 105 10 etat997 := viaCut proj72 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil277 : ℕ := 0x81020408102040810204081020000001fc00001fc000fe0007f
def etat998 : List ℕ := [fil277,fil254,fil255,fil256,fil257,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1040 : Ban 105 10 etat998 := viaCut proj72 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil278 : ℕ := 0x81020408102040810204081020000001fc00001fc000fe03f80
def etat999 : List ℕ := [fil278,fil254,fil255,fil256,fil257,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1041 : Ban 105 10 etat999 := viaCut proj72 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil279 : ℕ := 0x10204081020408102040810204000000000000fe0007f01fc07f
def etat1000 : List ℕ := [fil254,fil279,fil255,fil256,fil257,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1042 : Ban 105 10 etat1000 := viaCut proj73 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil280 : ℕ := 0x1020408102040810204081020400000fe00000000007f01fc07f
def etat1001 : List ℕ := [fil254,fil280,fil255,fil256,fil257,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1043 : Ban 105 10 etat1001 := viaCut proj73 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil281 : ℕ := 0x1020408102040810204081020400000fe00000fe0000001fc07f
def etat1002 : List ℕ := [fil254,fil281,fil255,fil256,fil257,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1044 : Ban 105 10 etat1002 := viaCut proj73 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil282 : ℕ := 0x1020408102040810204081020400000fe00000fe0007f000007f
def etat1003 : List ℕ := [fil254,fil282,fil255,fil256,fil257,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1045 : Ban 105 10 etat1003 := viaCut proj73 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil283 : ℕ := 0x1020408102040810204081020400000fe00000fe0007f01fc000
def etat1004 : List ℕ := [fil254,fil283,fil255,fil256,fil257,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1046 : Ban 105 10 etat1004 := viaCut proj72 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil284 : ℕ := 0x183060c183060c183060c1830600000fffc000fffc07ffffffff
def etat1005 : List ℕ := [fil254,fil255,fil284,fil256,fil257,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1047 : Ban 105 10 etat1005 := viaCut proj72 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil285 : ℕ := 0x2040810204081020408102040800000000007f0003f8001fff80
def etat1006 : List ℕ := [fil254,fil255,fil285,fil256,fil257,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1048 : Ban 105 10 etat1006 := viaCut proj74 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil286 : ℕ := 0x204081020408102040810204080007f00000000003f8001fff80
def etat1007 : List ℕ := [fil254,fil255,fil286,fil256,fil257,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1049 : Ban 105 10 etat1007 := viaCut proj74 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil287 : ℕ := 0x204081020408102040810204080007f000007f000000001fff80
def etat1008 : List ℕ := [fil254,fil255,fil287,fil256,fil257,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1050 : Ban 105 10 etat1008 := viaCut proj74 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil288 : ℕ := 0x204081020408102040810204080007f000007f0003f800003f80
def etat1009 : List ℕ := [fil254,fil255,fil288,fil256,fil257,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1051 : Ban 105 10 etat1009 := viaCut proj73 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil289 : ℕ := 0x204081020408102040810204080007f000007f0003f8001fc000
def etat1010 : List ℕ := [fil254,fil255,fil289,fil256,fil257,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1052 : Ban 105 10 etat1010 := viaCut proj72 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil290 : ℕ := 0x2850a142850a142850a142850a0007f01fc07f01fff80fffffff
def etat1011 : List ℕ := [fil254,fil255,fil256,fil290,fil257,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1053 : Ban 105 10 etat1011 := viaCut proj72 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil291 : ℕ := 0x3060c183060c183060c183060c0007ffe0007ffe03fff01fffff
def etat1012 : List ℕ := [fil254,fil255,fil256,fil291,fil257,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1054 : Ban 105 10 etat1012 := viaCut proj73 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil292 : ℕ := 0x40810204081020408102040810000000003f800003ffffe00000
def etat1013 : List ℕ := [fil254,fil255,fil256,fil292,fil257,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1055 : Ban 105 10 etat1013 := viaCut proj75 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil293 : ℕ := 0x4081020408102040810204081003f8000000000003ffffe00000
def etat1014 : List ℕ := [fil254,fil255,fil256,fil293,fil257,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1056 : Ban 105 10 etat1014 := viaCut proj75 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil294 : ℕ := 0x4081020408102040810204081003f800003f80000007ffe00000
def etat1015 : List ℕ := [fil254,fil255,fil256,fil294,fil257,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1057 : Ban 105 10 etat1015 := viaCut proj74 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil295 : ℕ := 0x4081020408102040810204081003f800003f800003f80fe00000
def etat1016 : List ℕ := [fil254,fil255,fil256,fil295,fil257,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1058 : Ban 105 10 etat1016 := viaCut proj73 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil296 : ℕ := 0x4081020408102040810204081003f800003f800003fff0000000
def etat1017 : List ℕ := [fil254,fil255,fil256,fil296,fil257,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1059 : Ban 105 10 etat1017 := viaCut proj72 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil297 : ℕ := 0x4891224489122448912244891203f8001fff8001ffffffe03fff
def etat1018 : List ℕ := [fil254,fil255,fil256,fil257,fil297,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1060 : Ban 105 10 etat1018 := viaCut proj72 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil298 : ℕ := 0x50a142850a142850a142850a1403f80fe03f80fe03ffffffc07f
def etat1019 : List ℕ := [fil254,fil255,fil256,fil257,fil298,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1061 : Ban 105 10 etat1019 := viaCut proj73 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil299 : ℕ := 0x60c183060c183060c183060c1803fff0003fff0003ffffffff80
def etat1020 : List ℕ := [fil254,fil255,fil256,fil257,fil299,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1062 : Ban 105 10 etat1020 := viaCut proj74 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil300 : ℕ := 0x81020408102040810204081020000000003ffffffc0000000000
def etat1021 : List ℕ := [fil254,fil255,fil256,fil257,fil300,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1063 : Ban 105 10 etat1021 := viaCut proj76 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil301 : ℕ := 0x81020408102040810204081021fc000000007ffffc0000000000
def etat1022 : List ℕ := [fil254,fil255,fil256,fil257,fil301,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1064 : Ban 105 10 etat1022 := viaCut proj75 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil302 : ℕ := 0x81020408102040810204081021fc0000003f80fffc0000000000
def etat1023 : List ℕ := [fil254,fil255,fil256,fil257,fil302,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1065 : Ban 105 10 etat1023 := viaCut proj74 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil303 : ℕ := 0x81020408102040810204081021fc0000003fff01fc0000000000
def etat1024 : List ℕ := [fil254,fil255,fil256,fil257,fil303,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1066 : Ban 105 10 etat1024 := viaCut proj73 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil304 : ℕ := 0x81020408102040810204081021fc0000003ffffe000000000000
def etat1025 : List ℕ := [fil254,fil255,fil256,fil257,fil304,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1067 : Ban 105 10 etat1025 := viaCut proj72 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil305 : ℕ := 0x89122448912244891224489123fc00001ffffffffc000fe03fff
def etat1026 : List ℕ := [fil254,fil255,fil256,fil257,fil258,fil305,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1068 : Ban 105 10 etat1026 := viaCut proj72 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil306 : ℕ := 0x91224489122448912244891225fc000fe03ffffffc07f01fc07f
def etat1027 : List ℕ := [fil254,fil255,fil256,fil257,fil258,fil306,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1069 : Ban 105 10 etat1027 := viaCut proj73 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil307 : ℕ := 0xa142850a142850a142850a1429fc07f0003ffffffff8001fff80
def etat1028 : List ℕ := [fil254,fil255,fil256,fil257,fil258,fil307,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1070 : Ban 105 10 etat1028 := viaCut proj74 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil308 : ℕ := 0xc183060c183060c183060c1831fff800003fffffffffffe00000
def etat1029 : List ℕ := [fil254,fil255,fil256,fil257,fil258,fil308,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1071 : Ban 105 10 etat1029 := viaCut proj75 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil309 : ℕ := 0x10204081020408102040810204003ffffffc00000000000000000
def etat1030 : List ℕ := [fil254,fil255,fil256,fil257,fil258,fil309,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1072 : Ban 105 10 etat1030 := viaCut proj76 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil310 : ℕ := 0x102040810204081020408102041fc07ffffc00000000000000000
def etat1031 : List ℕ := [fil254,fil255,fil256,fil257,fil258,fil310,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1073 : Ban 105 10 etat1031 := viaCut proj75 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil311 : ℕ := 0x102040810204081020408102041fff80fffc00000000000000000
def etat1032 : List ℕ := [fil254,fil255,fil256,fil257,fil258,fil311,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1074 : Ban 105 10 etat1032 := viaCut proj74 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil312 : ℕ := 0x102040810204081020408102041fffff01fc00000000000000000
def etat1033 : List ℕ := [fil254,fil255,fil256,fil257,fil258,fil312,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1075 : Ban 105 10 etat1033 := viaCut proj73 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil313 : ℕ := 0x102040810204081020408102041ffffffe0000000000000000000
def etat1034 : List ℕ := [fil254,fil255,fil256,fil257,fil258,fil313,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1076 : Ban 105 10 etat1034 := viaCut proj72 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil314 : ℕ := 0x10a142850a142850a142850a143ffffffffc00001fc000fe03fff
def etat1035 : List ℕ := [fil254,fil255,fil256,fil257,fil258,fil259,fil314]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1077 : Ban 105 10 etat1035 := viaCut proj72 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil315 : ℕ := 0x112244891224489122448912245ffffffffc000fe0007f01fc07f
def etat1036 : List ℕ := [fil254,fil255,fil256,fil257,fil258,fil259,fil315]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1078 : Ban 105 10 etat1036 := viaCut proj73 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil316 : ℕ := 0x122448912244891224489122449ffffffffc07f0003f8001fff80
def etat1037 : List ℕ := [fil254,fil255,fil256,fil257,fil258,fil259,fil316]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1079 : Ban 105 10 etat1037 := viaCut proj74 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil317 : ℕ := 0x142850a142850a142850a142851ffffffffff800003ffffe00000
def etat1038 : List ℕ := [fil254,fil255,fil256,fil257,fil258,fil259,fil317]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1080 : Ban 105 10 etat1038 := viaCut proj75 cinq (by decide) (by decide +kernel) (by decide +kernel)
def fil318 : ℕ := 0x183060c183060c183060c183061fffffffffffffffc0000000000
def etat1039 : List ℕ := [fil254,fil255,fil256,fil257,fil258,fil259,fil318]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1081 : Ban 105 10 etat1039 := viaCut proj76 cinq (by decide) (by decide +kernel) (by decide +kernel)
def etat1040 : List ℕ := [fil254,fil255,fil256,fil257,fil258,fil259]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1021 : Ban 105 11 etat1040 := viaBranch (ws := [etat980,etat981,etat982,etat983,etat984,etat985,etat986,etat987,etat988,etat989,etat990,etat991,etat992,etat993,etat994,etat995,etat996,etat997,etat998,etat999,etat1000,etat1001,etat1002,etat1003,etat1004,etat1005,etat1006,etat1007,etat1008,etat1009,etat1010,etat1011,etat1012,etat1013,etat1014,etat1015,etat1016,etat1017,etat1018,etat1019,etat1020,etat1021,etat1022,etat1023,etat1024,etat1025,etat1026,etat1027,etat1028,etat1029,etat1030,etat1031,etat1032,etat1033,etat1034,etat1035,etat1036,etat1037,etat1038,etat1039])
  (consBan preuve1022 (consBan preuve1023 (consBan preuve1024 (consBan preuve1025 (consBan preuve1026 (consBan preuve1027 (consBan preuve1028 (consBan preuve1029 (consBan preuve1030 (consBan preuve1031 (consBan preuve1032 (consBan preuve1033 (consBan preuve1034 (consBan preuve1035 (consBan preuve1036 (consBan preuve1037 (consBan preuve1038 (consBan preuve1039 (consBan preuve1040 (consBan preuve1041 (consBan preuve1042 (consBan preuve1043 (consBan preuve1044 (consBan preuve1045 (consBan preuve1046 (consBan preuve1047 (consBan preuve1048 (consBan preuve1049 (consBan preuve1050 (consBan preuve1051 (consBan preuve1052 (consBan preuve1053 (consBan preuve1054 (consBan preuve1055 (consBan preuve1056 (consBan preuve1057 (consBan preuve1058 (consBan preuve1059 (consBan preuve1060 (consBan preuve1061 (consBan preuve1062 (consBan preuve1063 (consBan preuve1064 (consBan preuve1065 (consBan preuve1066 (consBan preuve1067 (consBan preuve1068 (consBan preuve1069 (consBan preuve1070 (consBan preuve1071 (consBan preuve1072 (consBan preuve1073 (consBan preuve1074 (consBan preuve1075 (consBan preuve1076 (consBan preuve1077 (consBan preuve1078 (consBan preuve1079 (consBan preuve1080 (consBan preuve1081 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem six : Wide 105 11 etat1040 := widen (by decide +kernel) preuve1021
def fil319 : ℕ := 0x102040810204081020408102040000001fc00001fc000fe03fff
def fil320 : ℕ := 0x200000000000000000000000000
def fil321 : ℕ := 0x2040810204081020408102040800000fe00000fe0007f01fc07f
def fil322 : ℕ := 0x408102040810204081020408100007f000007f0003f8001fff80
def fil323 : ℕ := 0x8102040810204081020408102003f800003f800003ffffe00000
def fil324 : ℕ := 0x902040810204081020408102043fc0000003ffffffc0000000000
def fil325 : ℕ := 0x204081020408102040810204081ffffffffc00000000000000000
def etat1041 : List ℕ := [fil319,fil320,fil321,fil322,fil323,fil324,fil325]
def proj77 : Projection 106 105 := pick [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem preuve1082 : Ban 106 12 etat1041 := viaCut proj77 six (by decide) (by decide +kernel) (by decide +kernel)
theorem sept : Ban 106 12 etat1041 := preuve1082
def graph (x : Fin 7 → Bool) := decide (∃ i < ([0, 2, 0, 3, 2, 3, 0, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 2, 3, 0, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 2, 3, 0, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
def posBits : ℕ := 0x1160c183060c182850a142850a12244891224488912244891224183060c1830583060c183060a142850a14284891224489122142850a14284c183060c183050a142850a142244891224488c183060c1830489122448912142850a14285
def negBits : ℕ := 0x100080808080804040404040402020202020201010101010100808080808080404040404040202020202020101010101010080808080808040404040404020202020202010101010101008080808080804040404040402020202020201
def sample (bank : ℕ) (i : Fin 106) (j : Fin 7) := bank.testBit (7*i.val+j.val)
def inputs : List ℕ := etat1041
def seeds : List Wire := inputs.map (fun a => (false,a))
set_option maxHeartbeats 1000000 in
theorem listed : ∀ i : Fin 106, seeds.map (read i.val)=List.ofFn (sample posBits i) ∧
    seeds.map (read (106+i.val))=List.ofFn (sample negBits i) := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem labels : ∀ i : Fin 106, graph (sample posBits i)=true ∧ graph (sample negBits i)=false := by decide +kernel
theorem essential : ∀ a∈inputs, ∃ i : Fin 106, ∀ b∈inputs, b.testBit i.val≠b.testBit (106+i.val) → b=a := by decide +kernel
theorem initial {k S} (live : Live 106 k S) (sub : ∀ a∈S,a∈inputs) : S=inputs.toFinset := by
  apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
  intro a ha
  obtain ⟨i,h⟩ := essential a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
  exact h b (sub b hb) sep ▸ hb
theorem trace (C : Circuit) (fan : FanInTwo C) (eq : circuitFun 7 C=graph) :
    ∃ k≤C.gates.countP counted, Live 106 k inputs.toFinset := by
  let final := execute C.gates seeds
  let out := final.getD C.output zero
  have ev (i : ℕ) : read i out = C.eval (seeds.map (read i)) := by
    rw [show read i out = (final.map (read i)).getD C.output false from (read_get i final C.output).symm]
    rw [show final=execute C.gates seeds from rfl,execute_read i _ _ fan];rfl
  have result (x : Fin 7 → Bool) : C.eval (List.ofFn x)=graph x := congrFun eq x
  have good : Good 106 out.2 := by
    intro i hi same
    let j : Fin 106 := ⟨i,hi⟩
    have diff : read i out=read (106+i) out := by simp [read,same]
    have p := ev i;have n := ev (106+i)
    rw [(listed j).1,result,(labels j).1] at p
    rw [(listed j).2,result,(labels j).2] at n
    rw [p,n] at diff;contradiction
  have nz : out.2≠0 := by
    intro z;have bad := good 0 (by decide);simp [z] at bad
  have found : out.2∈ reps final := (get_simple final C.output).resolve_left nz
  obtain ⟨k,S,limit,live,sub⟩ := extract good nz C.gates seeds found
  have stays : ∀ a∈S, a∈inputs := by simpa [reps,seeds,List.map_map,Function.comp_def] using sub
  exact ⟨k,limit,initial live stays ▸ live⟩


def temoin : List Gate := [⟨.or,[0,2]⟩,⟨.and,[0,2]⟩,⟨.or,[3,4]⟩,⟨.and,[3,4]⟩,⟨.and,[7,9]⟩,⟨.or,[8,10]⟩,⟨.or,[11,12]⟩,⟨.or,[7,9]⟩,⟨.or,[1,14]⟩,⟨.or,[5,6]⟩,⟨.and,[5,6]⟩,⟨.and,[15,16]⟩,⟨.or,[17,18]⟩,⟨.or,[13,19]⟩]
theorem temoin_ok : ∀ g ∈ temoin, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by simp [temoin]
set_option maxHeartbeats 2000000 in
theorem temoin_calc : ∀ x : Fin 7 → Bool, Circuit.eval ⟨temoin,20⟩ (List.ofFn x) = graph x := by decide +kernel
theorem lt_count {gs : List Gate} (h : ∃ g ∈ gs, g.op = .not) : gs.countP counted < gs.length := by
  apply Nat.lt_of_le_of_ne List.countP_le_length
  intro eq
  obtain ⟨g,hg,hop⟩ := h
  have bad := List.countP_eq_length.mp eq g hg
  simp [counted,hop] at bad

end PEqualNP.Outside.L_meta_10532

open PEqualNP.Outside.L_meta_10532 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in

theorem PEqualNP.Outside.L_meta_10532 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 2, 3, 0, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 2, 3, 0, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 2, 3, 0, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 2, 3, 0, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 2, 3, 0, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 2, 3, 0, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o hfan _ he
  by_cases hn : ∃ g ∈ gs, g.op = .not
  · have fan : FanInTwo ⟨gs,o⟩ := fun g hg => ⟨(hfan g hg).1,(hfan g hg).2⟩
    obtain ⟨k,kle,live⟩ := trace ⟨gs,o⟩ fan (funext he)
    have grand : 13 ≤ k := by
      by_contra! small
      exact sept k (by omega) live
    have less := lt_count hn
    change k ≤ gs.countP counted at kle
    exact ⟨temoin,20,temoin_ok,by change 14 ≤ gs.length; omega,temoin_calc⟩
  · refine ⟨gs,o,?_,le_rfl,he⟩
    intro g hg
    exact ⟨(hfan g hg).1.imp_right (fun h => h.resolve_right (fun e => hn ⟨g,hg,e⟩)),(hfan g hg).2⟩

