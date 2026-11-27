import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_11615

-- The bounded trace proof uses the finite certificate from L_meta_11201.
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

def caseInputs : List ℕ := [14321620810927683078555195454553984,5203076698397949180363034373144703,4503599627370496,278925624339619598929174628106240,324518553658426747049354343743488,800516538214648786339548532572160,2782908631722995622493242261503]
def projectRows : Projection 57 50 := pick [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49] rfl (by decide +kernel) (by decide)
theorem caseBound : Ban 57 8 caseInputs := viaCut projectRows borne91 (by decide) (by decide +kernel) (by decide +kernel)
def graph (x : Fin 7 → Bool) := decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
def posBits : ℕ := 0x4144444a424254a954ab468468f0e1c4891224489122162c4891224489132a4489122448910e0c183060c1830a142850a142
def negBits : ℕ := 0x104040a020214215029460420d0e0c0a10e04028182140d421c0284030229421c028403800d421c02818180a10e0140c140
def sample (bank : ℕ) (i : Fin 57) (j : Fin 7) := bank.testBit (7*i.val+j.val)
def inputs : List ℕ := caseInputs
def seeds : List Wire := inputs.map (fun a => (false,a))
set_option maxHeartbeats 1000000 in
theorem listed : ∀ i : Fin 57, seeds.map (read i.val)=List.ofFn (sample posBits i) ∧
    seeds.map (read (57+i.val))=List.ofFn (sample negBits i) := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem labels : ∀ i : Fin 57, graph (sample posBits i)=true ∧ graph (sample negBits i)=false := by decide +kernel
theorem essential : ∀ a∈inputs, ∃ i : Fin 57, ∀ b∈inputs, b.testBit i.val≠b.testBit (57+i.val) → b=a := by decide +kernel
theorem initial {k S} (live : Live 57 k S) (sub : ∀ a∈S,a∈inputs) : S=inputs.toFinset := by
  apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
  intro a ha
  obtain ⟨i,h⟩ := essential a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
  exact h b (sub b hb) sep ▸ hb
theorem trace (C : Circuit) (fan : FanInTwo C) (eq : circuitFun 7 C=graph) :
    ∃ k≤C.gates.countP counted, Live 57 k inputs.toFinset := by
  let final := execute C.gates seeds
  let out := final.getD C.output zero
  have ev (i : ℕ) : read i out = C.eval (seeds.map (read i)) := by
    rw [show read i out = (final.map (read i)).getD C.output false from (read_get i final C.output).symm]
    rw [show final=execute C.gates seeds from rfl,execute_read i _ _ fan];rfl
  have result (x : Fin 7 → Bool) : C.eval (List.ofFn x)=graph x := congrFun eq x
  have good : Good 57 out.2 := by
    intro i hi same
    let j : Fin 57 := ⟨i,hi⟩
    have diff : read i out=read (57+i) out := by simp [read,same]
    have p := ev i;have n := ev (57+i)
    rw [(listed j).1,result,(labels j).1] at p
    rw [(listed j).2,result,(labels j).2] at n
    rw [p,n] at diff;contradiction
  have nz : out.2≠0 := by
    intro z;have bad := good 0 (by decide);simp [z] at bad
  have found : out.2∈ reps final := (get_simple final C.output).resolve_left nz
  obtain ⟨k,S,limit,live,sub⟩ := extract good nz C.gates seeds found
  have stays : ∀ a∈S, a∈inputs := by simpa [reps,seeds,List.map_map,Function.comp_def] using sub
  exact ⟨k,limit,initial live stays ▸ live⟩


def temoin : List Gate := [⟨.or, [1,2]⟩, ⟨.or, [0,1]⟩, ⟨.or, [0,6]⟩, ⟨.or, [4,6]⟩, ⟨.or, [5,6]⟩, ⟨.and, [9,3]⟩, ⟨.and, [10,8]⟩, ⟨.and, [11,7]⟩, ⟨.or, [12,13]⟩, ⟨.or, [15,14]⟩]
theorem temoin_ok : ∀ g ∈ temoin, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by simp [temoin]
set_option maxHeartbeats 2000000 in
theorem temoin_calc : ∀ x : Fin 7 → Bool, Circuit.eval ⟨temoin,16⟩ (List.ofFn x) = graph x := by decide +kernel
theorem lt_count {gs : List Gate} (h : ∃ g ∈ gs, g.op = .not) : gs.countP counted < gs.length := by
  apply Nat.lt_of_le_of_ne List.countP_le_length
  intro eq
  obtain ⟨g,hg,hop⟩ := h
  have bad := List.countP_eq_length.mp eq g hg
  simp [counted,hop] at bad

end PEqualNP.Outside.L_meta_11615

open PEqualNP.Outside.L_meta_11615 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in

theorem PEqualNP.Outside.L_meta_11615 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o hfan _ he
  by_cases hn : ∃ g ∈ gs, g.op = .not
  · have fan : FanInTwo ⟨gs,o⟩ := fun g hg => ⟨(hfan g hg).1,(hfan g hg).2⟩
    obtain ⟨k,kle,live⟩ := trace ⟨gs,o⟩ fan (funext he)
    have grand : 9 ≤ k := by
      by_contra! small
      exact caseBound k (by omega) live
    have less := lt_count hn
    change k ≤ gs.countP counted at kle
    exact ⟨temoin,16,temoin_ok,by change 10 ≤ gs.length; omega,temoin_calc⟩
  · refine ⟨gs,o,?_,le_rfl,he⟩
    intro g hg
    exact ⟨(hfan g hg).1.imp_right (fun h => h.resolve_right (fun e => hn ⟨g,hg,e⟩)),(hfan g hg).2⟩

