import PEqualNP.Defs

-- The signed live-wire calculus follows L-meta-10532 and L-meta-12325.

namespace PEqualNP.Outside.L_meta_14954

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

end PEqualNP.Outside.L_meta_14954

namespace PEqualNP.Outside.L_meta_14954

def opB (d : ℕ) (a b : Bool) : Bool :=
  match d with
  | 0 => a && b
  | 1 => a || b
  | 2 => a && !b
  | _ => b && !a
theorem combineBit (d a b i : ℕ) (hd : d<4) :
    (combine d a b).testBit i = opB d (a.testBit i) (b.testBit i) := by
  interval_cases d <;> cases ha : a.testBit i <;> cases hb : b.testBit i <;>
    simp [combine,opB,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,ha,hb]
def remap (d : ℕ) (s t : Bool) : ℕ :=
  let f := fun x y => opB d s t != opB d (s != x) (t != y)
  if f true false then (if f false true then 1 else 2) else (if f false true then 3 else 0)
theorem remapRule (d : ℕ) (hd : d<4) (s t x y : Bool) :
    remap d s t < 4 ∧
    (opB d s t != opB d x y) = opB (remap d s t) (s != x) (t != y) := by
  interval_cases d <;> cases s <;> cases t <;> cases x <;> cases y <;> decide

def signedBits (origin : ℕ) (w : ℕ) : List ℕ → ℕ
  | [] => 0
  | i::is => Nat.bit (w.testBit origin != w.testBit i) (signedBits origin w is)
theorem signedBit (origin w : ℕ) (is : List ℕ) (k : ℕ) :
    (signedBits origin w is).testBit k =
      (is[k]?.map (fun i => w.testBit origin != w.testBit i)).getD false := by
  induction is generalizing k with
  | nil => simp [signedBits]
  | cons i is ih =>
    cases k with
    | zero => cases ha : w.testBit origin <;> cases hb : w.testBit i <;> simp [signedBits,ha,hb]
    | succ k => simp [signedBits,Nat.testBit_bit_succ,ih]

structure Weak (m h : ℕ) where
  f : ℕ → ℕ
  good : ∀ w, Good m w → Good h (f w)
  pos : 0<h
  maps : ∀ d a b, d<4 → ∃ e, e<4 ∧ f (combine d a b)=combine e (f a) (f b)

def signedPick {m h : ℕ} (origin : ℕ) (r : List ℕ) (len : r.length=h)
    (small : ∀ i∈r,i<m) (pos : 0<h) : Weak m h := by
  let is := r ++ r.map (m+·)
  refine ⟨fun w => signedBits origin w is, ?_, pos, ?_⟩
  · intro a ha i hi
    have ir : i<r.length := by omega
    have diff := ha r[i] (small _ (List.getElem_mem ir))
    have H₁ : is[i]? = some r[i] := by simp [is,List.getElem?_append,ir]
    have H₂ : is[h+i]? = some (m+r[i]) := by
      have ne : ¬h+i<r.length := by omega
      have sub : h+i-r.length=i := by omega
      simp [is,List.getElem?_append,ne,sub,ir]
    simp only [signedBit,H₁,H₂,Option.map_some,Option.getD_some]
    cases a.testBit origin <;> simpa using diff
  · intro d a b hd
    let e := remap d (a.testBit origin) (b.testBit origin)
    have he : e<4 := (remapRule d hd _ _ false false).1
    refine ⟨e,he,Nat.eq_of_testBit_eq ?_⟩
    intro i
    rw [combineBit _ _ _ _ he]
    simp only [signedBit]
    cases hi : is[i]? with
    | none => interval_cases e <;> rfl
    | some j =>
      simp only [Option.map_some,Option.getD_some,combineBit _ _ _ _ hd]
      exact (remapRule d hd _ _ _ _).2

end PEqualNP.Outside.L_meta_14954

namespace PEqualNP.Outside.L_meta_14954
lemma weakCharge {m h d a b : ℕ} (p : Weak m h) (hd : d<4) (U : Finset ℕ)
    (fz : combine d a b∉insert a (insert b U)) (av : List ℕ) (ma : p.f a∈av) (mb : p.f b∈av) :
    (charge av (p.f (combine d a b))).toNat + dead p.f (insert a (insert b U)) ≤
      1+dead p.f (insert (combine d a b) U) := by
  obtain ⟨e,he,eq⟩ := p.maps d a b hd
  have up := deadMono p.f (combine d a b) U
  have la := deadLimit p.f a (insert b U)
  have lb := deadLimit p.f b U
  have free (bad : p.f a=0 ∨ p.f b=0) : charge av (p.f (combine d a b))=false := by
    rw [eq]
    rcases combine_eq_cases _ _ _ he (bad.imp_right Or.inl) with e|e|e <;> simp [charge,e,ma,mb]
  by_cases az : p.f a=0
  · rw [free (Or.inl az)];simp only [Bool.toNat_false,Nat.zero_add]
    by_cases bz : p.f b=0
    · have zz : p.f (combine d a b)=0 := by
        rw [eq,az,bz];interval_cases e <;> decide
      have fresh : combine d a b∉U := fun m => fz (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
      rw [deadGrow zz fresh];omega
    · rw [deadStay bz] at la;omega
  · rw [deadStay az]
    by_cases bz : p.f b=0
    · rw [free (Or.inr bz)];simp only [Bool.toNat_false,Nat.zero_add];omega
    · rw [deadStay bz];cases charge av (p.f (combine d a b)) <;> simp [Bool.toNat] <;> omega

theorem weakLive {m h k S} (p : Weak m h) (live : Live m k S) :
    ∃ j T,j+dead p.f S≤k ∧ Live h j T ∧ ∀ x∈T,x∈S.image p.f := by
  induction k generalizing S with
  | zero =>
    rw [Live] at live
    obtain ⟨a, rfl, hg, _⟩ := live
    have gp := p.good a hg
    have nz : p.f a≠0 := by intro e;have x := gp 0 p.pos;simp [e] at x
    exact ⟨0,{p.f a},by simp [dead,nz],Live.done gp nz,by simp⟩
  | succ k ih =>
    rw [Live] at live
    obtain ⟨U, a, b, d, rfl, hd, ha, hb, ab, fz, tail⟩ := live
    obtain ⟨j,T,cost,ok,raw⟩ := ih tail
    obtain ⟨e,he,eq⟩ := p.maps d a b hd
    let av := ((insert a (insert b U)).image p.f).toList
    have ma : p.f a∈av := by simp [av]
    have mb : p.f b∈av := by simp [av]
    have later : Possible h j (av++[combine e (p.f a) (p.f b)]) := by
      refine ⟨j,T,le_rfl,ok,?_⟩
      intro z hz
      have has := raw _ hz
      simp only [Finset.image_insert,Finset.mem_insert] at has
      rcases has with rfl|old
      · simp [eq]
      · have inav : z∈av := by simpa [av] using (Or.inr (Or.inr old) : z=p.f a ∨ z=p.f b ∨ z∈U.image p.f)
        simp [inav]
    obtain ⟨l,V,lim,good,sub⟩ := pullPaid he ma mb later
    rw [←eq] at lim
    have bound := weakCharge p hd U fz av ma mb
    exact ⟨l,V,by omega,good,by simpa [av] using sub⟩







end PEqualNP.Outside.L_meta_14954

namespace PEqualNP.Outside.L_meta_14954

theorem forced (d : ℕ) (hd : d<4) (left : Bool) :
    ∃ s c : Bool, ∀ y : Bool, (if left then opB d s y else opB d y s)=c := by
  interval_cases d <;> cases left <;> decide

theorem signedZero {o w : ℕ} {is : List ℕ} (same : ∀ i∈is, w.testBit i = w.testBit o) :
    signedBits o w is=0 := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    have hi := same i (by simp)
    have ht := ih (fun j hj => same j (by simp [hj]))
    simp [signedBits,hi,ht]

theorem forcedLeft {o v b d : ℕ} {is : List ℕ} {s c : Bool} (hd : d<4)
    (base : v.testBit o=s) (constant : ∀ i∈is, v.testBit i=s)
    (force : ∀ y, opB d s y=c) : signedBits o (combine d v b) is=0 := by
  apply signedZero
  intro i hi
  simp [combineBit _ _ _ _ hd,base,constant i hi,force]

theorem forcedRight {o v a d : ℕ} {is : List ℕ} {s c : Bool} (hd : d<4)
    (base : v.testBit o=s) (constant : ∀ i∈is, v.testBit i=s)
    (force : ∀ y, opB d y s=c) : signedBits o (combine d a v) is=0 := by
  apply signedZero
  intro i hi
  simp [combineBit _ _ _ _ hd,base,constant i hi,force]
end PEqualNP.Outside.L_meta_14954

namespace PEqualNP.Outside.L_meta_14954

theorem doubleElim {m h k S} (p : Bool → Weak m h) (v : ℕ)
    (killed : ∀ d a b, d<4 → (v=a ∨ v=b) → ∃ t, (p t).f (combine d a b)=0)
    (fixed : ∀ t, (p t).f v=0)
    (live : Live m k S) (hv : v∈S) :
    ∃ t j T, j+2≤k ∧ Live h j T ∧ ∀ x∈T,x∈S.image (p t).f := by
  induction k generalizing S with
  | zero =>
    rw [Live] at live
    obtain ⟨a,rfl,good,_⟩ := live
    have ev : v=a := by simpa using hv
    have bad := (p false).good a good 0 (p false).pos
    rw [←ev,fixed] at bad
    simp at bad
  | succ k ih =>
    rw [Live] at live
    obtain ⟨U,a,b,d,rfl,hd,_,_,_,_,tail⟩ := live
    by_cases hit : v=a ∨ v=b
    · obtain ⟨t,van⟩ := killed d a b hd hit
      obtain ⟨j,T,cost,ok,sub⟩ := weakLive (p t) tail
      have one : 0<dead (p t).f (insert (combine d a b) U) :=
        Finset.card_pos.mpr ⟨combine d a b,Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _,van⟩⟩
      refine ⟨t,j,T,by omega,ok,?_⟩
      intro x hx
      have mem := sub x hx
      rw [Finset.image_insert] at mem
      rcases Finset.mem_insert.mp mem with eq|mem
      · exact False.elim (liveNonzero ok x hx (eq.trans van))
      · simp [mem]
    · have vu : v∈U := by simpa [Finset.mem_insert,not_or.mp hit |>.1,not_or.mp hit |>.2] using hv
      obtain ⟨t,j,T,cost,ok,sub⟩ := ih tail (Finset.mem_insert_of_mem vu)
      let q := p t
      obtain ⟨e,he,eq⟩ := q.maps d a b hd
      let av := ((insert a (insert b U)).image q.f).toList
      have ma : q.f a∈av := by simp [av]
      have mb : q.f b∈av := by simp [av]
      have later : Possible h j (av++[combine e (q.f a) (q.f b)]) := by
        refine ⟨j,T,le_rfl,ok,?_⟩
        intro z hz
        have mem := sub z hz
        change z ∈ (insert (combine d a b) U).image q.f at mem
        rw [Finset.image_insert] at mem
        rcases Finset.mem_insert.mp mem with rfl|mem
        · simp [eq]
        · have inav : z∈av := by simp [av,mem]
          simp [inav]
      obtain ⟨l,V,lim,ok',sub'⟩ := pullPaid he ma mb later
      have cap : (charge av (combine e (q.f a) (q.f b))).toNat≤1 := by cases charge av _ <;> decide
      exact ⟨t,l,V,by omega,ok',by simpa [av,q] using sub'⟩
end PEqualNP.Outside.L_meta_14954

namespace PEqualNP.Outside.L_meta_14954
theorem viaWeakCut {m h f t : ℕ} {v w : List ℕ} (p : Weak m h)
    (bound : Wide h t w) (nd : v.Nodup)
    (mem : ∀ a∈v, p.f a=0 ∨ p.f a∈w)
    (cost : f≤t+(v.map p.f).count 0) : Ban m f v := by
  intro k lim run
  obtain ⟨j,T,c,ok,incl⟩ := weakLive p run
  have fixed : dead p.f v.toFinset=(v.map p.f).count 0 := by
    dsimp [dead]
    have E : v.toFinset.filter (fun x => p.f x=0) = (v.filter (fun x => decide (p.f x=0))).toFinset := by ext x;simp
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

end PEqualNP.Outside.L_meta_14954

namespace PEqualNP.Outside.L_meta_14954

abbrev Rule (m k : ℕ) := { test : List ℕ → Bool // ∀ v, v.Nodup → test v=true → Ban m k v }

def relaxed {m h} (p : Projection m h) : Weak m h :=
  ⟨p.val,p.property.2.2.1,p.property.2.2.2,fun d a b hd => ⟨d,hd,p.property.2.1 d a b hd⟩⟩

def cutRule {m h bound : ℕ} (k : ℕ) (p : Weak m h) {w : List ℕ} (lo : Wide h bound w) : Rule m k :=
  ⟨fun v => decide (k ≤ bound+(v.map p.f).count 0) && v.all (fun x => p.f x == 0 || w.contains (p.f x)), by
    intro v nd ok
    simp only [Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,Bool.or_eq_true,beq_iff_eq,List.contains_iff_mem] at ok
    exact viaWeakCut p lo nd ok.2 ok.1⟩

def fingerprint (v : List ℕ) : ℕ :=
  (v.map (fun x => ((x ^^^ (x >>> 23)) * (x+17)) % 2147483647)).sum % 2147483647

def dictionary {m k} (entries : List (ℕ × Rule m k)) : Rule m k :=
  ⟨fun v => entries.any (fun e => e.1 == fingerprint v && e.2.val v), by
    intro v nd yes
    obtain ⟨e,_,ok⟩ := List.any_eq_true.mp yes
    simp only [Bool.and_eq_true] at ok
    exact e.2.property v nd ok.2⟩

theorem viaRules {m f : ℕ} {v : List ℕ} {ws : List (List ℕ)} (closed : banList m f ws)
    (cuts : Rule m f) (nd : v.Nodup) (no : terminal m v=false)
    (test : anyGate m f (fun u => (!ws.contains (ordered u)) && (!cuts.val u) && search m f u) v=false) :
    Ban m (f+1) v := by
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
    have yes := @transition m f n U a b d v (fun u => (!ws.contains (ordered u)) && (!cuts.val u) && search m f u)
      hd ab fr rep nd (by omega) tail (by
      intro u hu nu
      simp only [Bool.and_eq_true]
      refine ⟨⟨?_,?_⟩,complete m f tail (by omega) u hu nu⟩
      · simp
        intro found
        have hv := closed _ found n (by omega)
        rw [ord_eq,hu] at hv
        exact hv tail
      · cases eq : cuts.val u with
        | false => rfl
        | true =>
          have bad := cuts.property u nu eq n (by omega)
          rw [hu] at bad
          exact False.elim (bad tail))
    simp_all
end PEqualNP.Outside.L_meta_14954

namespace PEqualNP.Outside.L_meta_14954.B0
def bank : List ℕ := [0x10412cc00029100555590412cc01069300ffff,0x28a305228b14cccccc028a30f269b1ccccccc,0x30c35028a3a0f0f0f0030c3f038e3e0f0f0f0,0x200e40040fc005500aaa00fc00c0fc00ff00ff,0x4390000bf0000aaaa0043f0000ff0000ffff00,0x6400000d5544a0000007c00000ffffff000000,0x18618aa0000000000007ffffff000000000000]
def f0 : ℕ := 0x14f
def f1 : ℕ := 0x4b3
def f2 : ℕ := 0xa3c
def s0 : List ℕ := [f0,f1,f2]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w0 : Wide 6 2 s0 := viaSearch (by decide +kernel)
def p0 : Weak 76 6 := relaxed (pick [16,17,58,59,64,65] (by decide) (by decide) (by decide))
def r0 : Rule 76 6 := cutRule 6 p0 w0
def f3 : ℕ := 0x2cf
def f4 : ℕ := 0x973
def f5 : ℕ := 0x143c
def s1 : List ℕ := [f3,f4,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w1 : Wide 7 3 s1 := viaSearch (by decide +kernel)
def p1 : Weak 76 7 := relaxed (pick [0,1,8,9,16,17,75] (by decide) (by decide) (by decide))
def r1 : Rule 76 6 := cutRule 6 p1 w1
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w2 : Wide 7 2 s1 := viaSearch (by decide +kernel)
def r2 : Rule 76 6 := cutRule 6 p1 w2
def f6 : ℕ := 0x2b53ff
def f7 : ℕ := 0x40ac1f
def f8 : ℕ := 0x940fe0
def s2 : List ℕ := [f6,f7,f8]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w3 : Wide 12 2 s2 := viaSearch (by decide +kernel)
def p2 : Weak 76 12 := relaxed (pick [26,27,29,30,32,48,49,52,53,56,70,71] (by decide) (by decide) (by decide))
def r3 : Rule 76 6 := cutRule 6 p2 w3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w4 : Wide 6 3 s0 := viaSearch (by decide +kernel)
def r4 : Rule 76 6 := cutRule 6 p0 w4
def f9 : ℕ := 0x38e3552aabb4fcfcfc038e3ff3efbfcfcfcfc
def f10 : ℕ := 0x10412cc00029100555590412cc01069300ffff
def f11 : ℕ := 0x18618aa0000000000007ffffff000000000000
def f12 : ℕ := 0x200e40040fc005500aaa00fc00c0fc00ff00ff
def f13 : ℕ := 0x4390000bf0000aaaa0043f0000ff0000ffff00
def f14 : ℕ := 0x6400000d5544a0000007c00000ffffff000000
def s3 : List ℕ := [f9,f10,f11,f12,f13,f14]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b1 : Ban 76 7 s3 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1814143857,r0),(1907166558,r1),(253080851,r0),(2017441422,r2),(322822113,r0),(561119641,r2),(1497603932,r3),(1565649687,r0),(699659911,r0),(1166650322,r0),(1921876841,r4)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r5 : Rule 76 7 := cutRule 7 p0 w4
def f15 : ℕ := 0xb4c
def f16 : ℕ := 0xeb0
def s4 : List ℕ := [f2,f15,f16]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w5 : Wide 6 3 s4 := viaSearch (by decide +kernel)
def p3 : Weak 76 6 := signedPick 4 [4,5,12,13,20,21] (by decide) (by decide) (by decide)
def r6 : Rule 76 7 := cutRule 7 p3 w5
def p4 : Weak 76 6 := signedPick 2 [2,3,10,11,18,19] (by decide) (by decide) (by decide)
def r7 : Rule 76 7 := cutRule 7 p4 w5
def f17 : ℕ := 0x11533f
def f18 : ℕ := 0x54cdcc
def f19 : ℕ := 0xaa0ff0
def f20 : ℕ := 0xe0ae0f
def s5 : List ℕ := [f17,f18,f19,f20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w6 : Wide 12 3 s5 := viaSearch (by decide +kernel)
def p5 : Weak 76 12 := relaxed (pick [8,9,10,11,24,25,26,27,28,40,41,42] (by decide) (by decide) (by decide))
def r8 : Rule 76 7 := cutRule 7 p5 w6
def p6 : Weak 76 6 := relaxed (pick [26,27,48,49,70,71] (by decide) (by decide) (by decide))
def r9 : Rule 76 7 := cutRule 7 p6 w0
def f21 : ℕ := 0x1451cf
def f22 : ℕ := 0x4a0ff0
def f23 : ℕ := 0x91c93c
def f24 : ℕ := 0xa0ae0f
def s6 : List ℕ := [f21,f22,f23,f24]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w7 : Wide 12 3 s6 := viaSearch (by decide +kernel)
def p7 : Weak 76 12 := relaxed (pick [16,17,18,19,48,49,58,59,61,64,65,67] (by decide) (by decide) (by decide))
def r10 : Rule 76 7 := cutRule 7 p7 w7
def f25 : ℕ := 0xb41fc
def f26 : ℕ := 0x20ae1f
def f27 : ℕ := 0x991993
def f28 : ℕ := 0xd40fe0
def s7 : List ℕ := [f25,f26,f27,f28]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w8 : Wide 12 3 s7 := viaSearch (by decide +kernel)
def p8 : Weak 76 12 := relaxed (pick [24,25,26,27,28,48,49,50,51,70,71,72] (by decide) (by decide) (by decide))
def r11 : Rule 76 7 := cutRule 7 p8 w8
def f29 : ℕ := 0x3c0
def f30 : ℕ := 0x8a23c
def f31 : ℕ := 0xbb6cc
def f32 : ℕ := 0xdeb70
def s8 : List ℕ := [f29,f30,f31,f32]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w9 : Wide 10 3 s8 := viaSearch (by decide +kernel)
def p9 : Weak 76 10 := signedPick 2 [2,3,10,11,18,19,48,50,61,67] (by decide) (by decide) (by decide)
def r12 : Rule 76 7 := cutRule 7 p9 w9
def r13 : Rule 76 7 := cutRule 7 p0 w0
def p10 : Weak 76 10 := signedPick 2 [2,3,10,11,18,19,26,28,35,41] (by decide) (by decide) (by decide)
def r14 : Rule 76 7 := cutRule 7 p10 w9
def f33 : ℕ := 0x4c54cf
def f34 : ℕ := 0x6a0ff0
def f35 : ℕ := 0x85c8fc
def f36 : ℕ := 0x90af0f
def s9 : List ℕ := [f33,f34,f35,f36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w10 : Wide 12 3 s9 := viaSearch (by decide +kernel)
def p11 : Weak 76 12 := relaxed (pick [8,9,10,11,48,49,50,51,64,65,66,67] (by decide) (by decide) (by decide))
def r15 : Rule 76 7 := cutRule 7 p11 w10
def f37 : ℕ := 0x98b4cf
def f38 : ℕ := 0xd40ff0
def f39 : ℕ := 0x10b88fc
def f40 : ℕ := 0x1215f0f
def s10 : List ℕ := [f37,f38,f39,f40]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w11 : Wide 13 3 s10 := viaSearch (by decide +kernel)
def p12 : Weak 76 13 := relaxed (pick [0,1,2,3,48,49,50,51,58,59,60,61,75] (by decide) (by decide) (by decide))
def r16 : Rule 76 7 := cutRule 7 p12 w11
def f41 : ℕ := 0x441561330ff
def f42 : ℕ := 0x9533306dcccc
def f43 : ℕ := 0x238142b8e0f0f
def f44 : ℕ := 0x5c02a81f00ff0
def f45 : ℕ := 0x76a8001fff000
def s11 : List ℕ := [f41,f42,f43,f44,f45]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w12 : Wide 26 5 s11 := viaSearch (by decide +kernel)
def p13 : Weak 76 26 := relaxed (pick [0,1,2,3,8,9,10,11,16,17,18,19,24,25,26,27,28,34,35,36,40,41,42,46,47,75] (by decide) (by decide) (by decide))
def r17 : Rule 76 7 := cutRule 7 p13 w12
def f46 : ℕ := 0x9115c0933fc
def f47 : ℕ := 0x24a000fff000
def f48 : ℕ := 0x4144c541cccf
def f49 : ℕ := 0x8a0b0a8e0f0f
def f50 : ℕ := 0xd00ea0f00ff0
def s12 : List ℕ := [f46,f47,f48,f49,f50]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w13 : Wide 24 5 s12 := viaSearch (by decide +kernel)
def p14 : Weak 76 24 := relaxed (pick [16,17,18,19,26,27,35,36,41,42,46,47,48,49,58,59,61,64,65,67,70,71,73,74] (by decide) (by decide) (by decide))
def r18 : Rule 76 7 := cutRule 7 p14 w13
def f51 : ℕ := 0x44115c04473fc
def f52 : ℕ := 0x3336000ffff000
def f53 : ℕ := 0x40484c54078ccf
def f54 : ℕ := 0x8480b0a8780f0f
def f55 : ℕ := 0xc800ea0f800ff0
def s13 : List ℕ := [f51,f52,f53,f54,f55]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w14 : Wide 28 5 s13 := viaSearch (by decide +kernel)
def p15 : Weak 76 28 := relaxed (pick [16,17,18,19,26,27,35,36,41,42,46,47,48,49,51,58,59,60,61,64,65,66,67,70,71,72,73,74] (by decide) (by decide) (by decide))
def r19 : Rule 76 7 := cutRule 7 p15 w14
def f56 : ℕ := 0x22b33f
def f57 : ℕ := 0xa98dcc
def f58 : ℕ := 0x1540ff0
def f59 : ℕ := 0x1c15e0f
def s14 : List ℕ := [f56,f57,f58,f59]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w15 : Wide 13 3 s14 := viaSearch (by decide +kernel)
def p16 : Weak 76 13 := relaxed (pick [0,1,2,3,24,25,26,27,28,34,35,36,75] (by decide) (by decide) (by decide))
def r20 : Rule 76 7 := cutRule 7 p16 w15
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w16 : Wide 6 2 s4 := viaSearch (by decide +kernel)
def r21 : Rule 76 7 := cutRule 7 p4 w16
def f60 : ℕ := 0x28a305228b14cccccc028a30f269b1ccccccc
def f61 : ℕ := 0x30c35028a3a0f0f0f0030c3f038e3e0f0f0f0
def s15 : List ℕ := [f10,f60,f61,f12,f13,f14,f11]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b0 : Ban 76 8 s15 := viaRules (ws := [s3]) (consBan b1 (nilBan _ _))
  (dictionary [(1913126464,r5),(1807972506,r5),(974805279,r6),(134077782,r7),(1695871083,r8),(700039971,r9),(1765612345,r10),(1330280848,r9),(1175054528,r11),(469543128,r10),(792910517,r8),(1148851990,r9),(1675132546,r11),(1103039784,r8),(2142450143,r12),(962333462,r13),(84619285,r12),(1541066533,r10),(217016188,r12),(147978745,r14),(1428122014,r12),(1692406883,r15),(2049568341,r12),(1487285108,r8),(37227170,r12),(1881079023,r16),(60000298,r12),(2097602038,r11),(377791675,r14),(1202473143,r17),(1057497151,r18),(1162956847,r14),(514010867,r19),(369034875,r10),(1079978565,r14),(296043948,r14),(1996297923,r14),(1410593247,r14),(1312748007,r14),(381495239,r8),(1025498339,r14),(237027033,r8),(2003909873,r14),(2082368265,r20),(1054440688,r14),(182578966,r11),(461956907,r14),(1217183426,r21),(1665486064,r14),(866688893,r12)])
  (by decide) (by decide +kernel) (by decide +kernel)
theorem cert6 : Ban 76 8 bank := b0
end PEqualNP.Outside.L_meta_14954.B0

namespace PEqualNP.Outside.L_meta_14954.B1
def bank : List ℕ := [0x8412cc00aa005555fff8412cc00aa00ffff,0x28a305aacccccccc00028a30faacccccccc,0x30c350ccf0f0f0f000030c3f0ccf0f0f0f0,0xe4000f005500aafff00fc000f00ff00ff,0x390000f000aaaa000003f0000f000ffff00,0xc00000ffff000000,0xc618aa0000000000000ffffff0000000000]
def f0 : ℕ := 0x14f
def f1 : ℕ := 0x4b3
def f2 : ℕ := 0xa3c
def s0 : List ℕ := [f0,f1,f2]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w0 : Wide 6 2 s0 := viaSearch (by decide +kernel)
def p0 : Weak 76 6 := relaxed (pick [16,17,50,51,56,57] (by decide) (by decide) (by decide))
def r0 : Rule 76 6 := cutRule 6 p0 w0
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w1 : Wide 6 3 s0 := viaSearch (by decide +kernel)
def r1 : Rule 76 6 := cutRule 6 p0 w1
def f3 : ℕ := 0xa9500fff80
def f4 : ℕ := 0xa9faa01f80
def f5 : ℕ := 0xff555fe000
def s1 : List ℕ := [f3,f4,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w2 : Wide 20 3 s1 := viaSearch (by decide +kernel)
def p1 : Weak 76 20 := signedPick 1 [1,2,3,4,5,6,7,10,11,12,13,14,15,16,18,19,20,21,22,23] (by decide) (by decide) (by decide)
def r2 : Rule 76 6 := cutRule 6 p1 w2
def f6 : ℕ := 0x3bd3ff
def f7 : ℕ := 0x402c1f
def f8 : ℕ := 0x840fe0
def s2 : List ℕ := [f6,f7,f8]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w3 : Wide 12 3 s2 := viaSearch (by decide +kernel)
def p2 : Weak 76 12 := relaxed (pick [16,17,18,20,22,50,51,53,54,55,56,57] (by decide) (by decide) (by decide))
def r3 : Rule 76 6 := cutRule 6 p2 w3
def f9 : ℕ := 0x12cc5512ccff
def f10 : ℕ := 0x18aa00ffff00
def f11 : ℕ := 0xe355fce3fffc
def f12 : ℕ := 0xe400aafc00ff
def s3 : List ℕ := [f9,f10,f11,f12]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w4 : Wide 24 3 s3 := viaSearch (by decide +kernel)
def p3 : Weak 76 24 := relaxed (pick [8,9,10,11,12,13,14,15,40,41,42,43,44,45,46,47,48,49,56,57,58,59,60,61] (by decide) (by decide) (by decide))
def r4 : Rule 76 6 := cutRule 6 p3 w4
def f13 : ℕ := 0x390015402abffc0fc00ff00ff
def f14 : ℕ := 0x104b30015557ffc412cc00ffff
def f15 : ℕ := 0x1862a8000000003fffff000000
def f16 : ℕ := 0xe38d57f3f3f00038e3fffcfcfc
def f17 : ℕ := 0xe40002aaa800003f0000ffff00
def f18 : ℕ := 0xe79003feaaabfffffc00ffffff
def s4 : List ℕ := [f13,f14,f15,f16,f17,f18]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w5 : Wide 58 5 s4 := viaSearch (by decide +kernel)
def p4 : Weak 76 58 := relaxed (pick [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,64,65,66,67,68,69,70,71,72,73,74,75] (by decide) (by decide) (by decide))
def r5 : Rule 76 6 := cutRule 6 p4 w5
def f19 : ℕ := 0xab540fffc0
def f20 : ℕ := 0xabfd501fc0
def f21 : ℕ := 0xff56afe000
def s5 : List ℕ := [f19,f20,f21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w6 : Wide 20 3 s5 := viaSearch (by decide +kernel)
def p5 : Weak 76 20 := signedPick 2 [2,3,4,5,6,7,9,10,11,12,13,14,15,17,18,19,20,21,22,23] (by decide) (by decide) (by decide)
def r6 : Rule 76 6 := cutRule 6 p5 w6
def f22 : ℕ := 0x2107f
def f23 : ℕ := 0x140fe0
def f24 : ℕ := 0xe9ef9f
def s6 : List ℕ := [f22,f23,f24]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w7 : Wide 12 3 s6 := viaSearch (by decide +kernel)
def p6 : Weak 76 12 := relaxed (pick [16,17,19,21,23,50,51,56,57,59,60,61] (by decide) (by decide) (by decide))
def r7 : Rule 76 6 := cutRule 6 p6 w7
def f25 : ℕ := 0x17ffcf
def f26 : ℕ := 0x4bfff3
def f27 : ℕ := 0xa0003c
def s7 : List ℕ := [f25,f26,f27]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w8 : Wide 18 2 s7 := viaSearch (by decide +kernel)
def p7 : Weak 76 18 := relaxed (pick [0,1,8,9,16,17,64,65,66,67,68,69,70,71,72,73,74,75] (by decide) (by decide) (by decide))
def r8 : Rule 76 6 := cutRule 6 p7 w8
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w9 : Wide 18 3 s7 := viaSearch (by decide +kernel)
def r9 : Rule 76 6 := cutRule 6 p7 w9
def f28 : ℕ := 0x1553ff
def f29 : ℕ := 0x4aacff
def f30 : ℕ := 0xa00f00
def s8 : List ℕ := [f28,f29,f30]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w10 : Wide 12 3 s8 := viaSearch (by decide +kernel)
def p8 : Weak 76 12 := relaxed (pick [16,17,18,19,20,21,22,23,50,51,56,57] (by decide) (by decide) (by decide))
def r10 : Rule 76 6 := cutRule 6 p8 w10
def f31 : ℕ := 0x5555fff00ffff
def f32 : ℕ := 0x5500aafffff00ff
def f33 : ℕ := 0xaaaa00000ffff00
def s9 : List ℕ := [f31,f32,f33]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w11 : Wide 36 3 s9 := viaSearch (by decide +kernel)
def p9 : Weak 76 36 := relaxed (pick [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,64,65,66,67,68,69,70,71,72,73,74,75] (by decide) (by decide) (by decide))
def r11 : Rule 76 6 := cutRule 6 p9 w11
def f34 : ℕ := 0x51f
def f35 : ℕ := 0x22e3
def f36 : ℕ := 0xd8fc
def s10 : List ℕ := [f34,f35,f36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w12 : Wide 8 3 s10 := viaSearch (by decide +kernel)
def p10 : Weak 76 8 := relaxed (pick [16,17,50,51,52,56,57,58] (by decide) (by decide) (by decide))
def r12 : Rule 76 6 := cutRule 6 p10 w12
def f37 : ℕ := 0xc00000ffff000000
def f38 : ℕ := 0xe4000f005500aafff00fc000f00ff00ff
def f39 : ℕ := 0x38e355eefcfcfcfc00038e3ffeefcfcfcfc
def f40 : ℕ := 0x390000f000aaaa000003f0000f000ffff00
def f41 : ℕ := 0x8412cc00aa005555fff8412cc00aa00ffff
def f42 : ℕ := 0xc618aa0000000000000ffffff0000000000
def s11 : List ℕ := [f37,f38,f39,f40,f41,f42]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b1 : Ban 76 7 s11 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(1151313487,r0),(1006958687,r1),(877899689,r1),(1970914000,r1),(1867706401,r0),(878304905,r0),(764962616,r1),(1193854368,r1),(1739847359,r0),(562831168,r2),(929429257,r3),(1212261037,r0),(536728767,r1),(776899790,r1),(669849363,r1),(1872970042,r0),(1451891424,r4),(1065989512,r5),(803932361,r6),(1770489302,r7),(1617060536,r0),(1662796724,r1),(151838033,r1),(1848426626,r0),(352374260,r0),(1262231233,r0),(1150966537,r0),(404589647,r1),(1538601260,r1),(1158506147,r1),(145034113,r1),(969029795,r0),(1708810128,r8),(1609011552,r9),(1212061069,r8),(420403304,r10),(138236790,r0),(756207655,r11),(474041141,r1),(118479602,r0),(648163475,r8),(540130457,r9),(492707136,r8),(2122960396,r9),(445522828,r1),(304400400,r1),(699837443,r12)])
  (by decide) (by decide +kernel) (by decide +kernel)
def r13 : Rule 76 7 := cutRule 7 p0 w1
def f43 : ℕ := 0xb4c
def f44 : ℕ := 0xeb0
def s12 : List ℕ := [f2,f43,f44]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w13 : Wide 6 3 s12 := viaSearch (by decide +kernel)
def p11 : Weak 76 6 := signedPick 4 [4,5,12,13,20,21] (by decide) (by decide) (by decide)
def r14 : Rule 76 7 := cutRule 7 p11 w13
def p12 : Weak 76 6 := signedPick 2 [2,3,10,11,18,19] (by decide) (by decide) (by decide)
def r15 : Rule 76 7 := cutRule 7 p12 w13
def f45 : ℕ := 0x21c
def f46 : ℕ := 0xa46b
def f47 : ℕ := 0x24993
def f48 : ℕ := 0xd03e0
def s13 : List ℕ := [f45,f46,f47,f48]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w14 : Wide 10 3 s13 := viaSearch (by decide +kernel)
def p13 : Weak 76 10 := relaxed (pick [16,17,24,32,36,50,51,56,57,62] (by decide) (by decide) (by decide))
def r16 : Rule 76 7 := cutRule 7 p13 w14
def f49 : ℕ := 0x20f0
def f50 : ℕ := 0x46b13ac
def f51 : ℕ := 0x53294c0
def f52 : ℕ := 0xa803f00
def f53 : ℕ := 0xacd6330
def s14 : List ℕ := [f49,f50,f51,f52,f53]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w15 : Wide 14 4 s14 := viaSearch (by decide +kernel)
def p14 : Weak 76 14 := signedPick 0 [0,1,2,3,8,10,16,18,42,43,50,52,53,58] (by decide) (by decide) (by decide)
def r17 : Rule 76 7 := cutRule 7 p14 w15
def f54 : ℕ := 0x4c54cf
def f55 : ℕ := 0x6a0ff0
def f56 : ℕ := 0x85c8fc
def f57 : ℕ := 0x90af0f
def s15 : List ℕ := [f54,f55,f56,f57]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w16 : Wide 12 3 s15 := viaSearch (by decide +kernel)
def p15 : Weak 76 12 := relaxed (pick [8,9,10,11,40,41,42,43,56,57,58,59] (by decide) (by decide) (by decide))
def r18 : Rule 76 7 := cutRule 7 p15 w16
def f58 : ℕ := 0x1f00
def f59 : ℕ := 0x21210f8
def f60 : ℕ := 0x2735318
def f61 : ℕ := 0x3bebde0
def s16 : List ℕ := [f58,f59,f60,f61]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w17 : Wide 13 4 s16 := viaSearch (by decide +kernel)
def p16 : Weak 76 13 := signedPick 1 [1,2,3,10,11,16,18,19,26,27,32,33,37] (by decide) (by decide) (by decide)
def r19 : Rule 76 7 := cutRule 7 p16 w17
def f62 : ℕ := 0x3c0
def f63 : ℕ := 0x8a23c
def f64 : ℕ := 0xbb6cc
def f65 : ℕ := 0xdeb70
def s17 : List ℕ := [f62,f63,f64,f65]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w18 : Wide 10 3 s17 := viaSearch (by decide +kernel)
def p17 : Weak 76 10 := signedPick 2 [2,3,10,11,18,19,26,27,33,37] (by decide) (by decide) (by decide)
def r20 : Rule 76 7 := cutRule 7 p17 w18
def f66 : ℕ := 0x4d37ff8fe7
def f67 : ℕ := 0x82800070f8
def f68 : ℕ := 0x2204fffc41f
def f69 : ℕ := 0x33000007f00
def s18 : List ℕ := [f66,f67,f68,f69]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w19 : Wide 27 4 s18 := viaSearch (by decide +kernel)
def p18 : Weak 76 27 := relaxed (pick [0,1,3,8,9,16,17,18,50,51,52,53,56,57,58,64,65,66,67,68,69,70,71,72,73,74,75] (by decide) (by decide) (by decide))
def r21 : Rule 76 7 := cutRule 7 p18 w19
def p19 : Weak 76 13 := signedPick 1 [1,4,5,12,13,16,20,21,28,29,32,34,38] (by decide) (by decide) (by decide)
def r22 : Rule 76 7 := cutRule 7 p19 w17
def p20 : Weak 76 10 := signedPick 4 [4,5,12,13,20,21,28,29,34,38] (by decide) (by decide) (by decide)
def r23 : Rule 76 7 := cutRule 7 p20 w18
def p21 : Weak 76 27 := relaxed (pick [0,1,5,8,9,16,17,20,50,51,52,54,56,57,58,64,65,66,67,68,69,70,71,72,73,74,75] (by decide) (by decide) (by decide))
def r24 : Rule 76 7 := cutRule 7 p21 w19
def f70 : ℕ := 0x5803f00
def f71 : ℕ := 0x86ca3b2
def f72 : ℕ := 0xa3a28c0
def f73 : ℕ := 0xa3a38fc
def f74 : ℕ := 0xffffb3c
def s19 : List ℕ := [f70,f71,f72,f73,f74]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w20 : Wide 14 4 s19 := viaSearch (by decide +kernel)
def p22 : Weak 76 14 := signedPick 0 [0,2,8,9,10,11,17,19,42,43,52,56,58,59] (by decide) (by decide) (by decide)
def r25 : Rule 76 7 := cutRule 7 p22 w20
def f75 : ℕ := 0x4c5fff4cf
def f76 : ℕ := 0x6a0000ff0
def f77 : ℕ := 0x85c0008fc
def f78 : ℕ := 0x90affff0f
def s20 : List ℕ := [f75,f76,f77,f78]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w21 : Wide 24 3 s20 := viaSearch (by decide +kernel)
def p23 : Weak 76 24 := relaxed (pick [0,1,2,3,40,41,42,43,50,51,52,53,64,65,66,67,68,69,70,71,72,73,74,75] (by decide) (by decide) (by decide))
def r26 : Rule 76 7 := cutRule 7 p23 w21
def f79 : ℕ := 0x31698fc
def f80 : ℕ := 0x377bb1c
def f81 : ℕ := 0x3bedde0
def s21 : List ℕ := [f58,f79,f80,f81]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w22 : Wide 13 4 s21 := viaSearch (by decide +kernel)
def p24 : Weak 76 13 := signedPick 2 [2,3,9,10,11,17,18,19,26,27,33,36,37] (by decide) (by decide) (by decide)
def r27 : Rule 76 7 := cutRule 7 p24 w22
def f82 : ℕ := 0x917ff87e3
def f83 : ℕ := 0x1202fffa41f
def f84 : ℕ := 0x1b000007f00
def f85 : ℕ := 0x246c00078fc
def s22 : List ℕ := [f82,f83,f84,f85]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w23 : Wide 27 4 s22 := viaSearch (by decide +kernel)
def p25 : Weak 76 27 := relaxed (pick [0,1,8,9,11,16,17,19,50,51,52,56,57,58,59,64,65,66,67,68,69,70,71,72,73,74,75] (by decide) (by decide) (by decide))
def r28 : Rule 76 7 := cutRule 7 p25 w23
def p26 : Weak 76 13 := signedPick 4 [4,5,9,12,13,17,20,21,28,29,34,36,38] (by decide) (by decide) (by decide)
def r29 : Rule 76 7 := cutRule 7 p26 w22
def p27 : Weak 76 27 := relaxed (pick [0,1,8,9,13,16,17,21,50,51,52,56,57,58,60,64,65,66,67,68,69,70,71,72,73,74,75] (by decide) (by decide) (by decide))
def r30 : Rule 76 7 := cutRule 7 p27 w23
def f86 : ℕ := 0x9050afff0f0f0f
def f87 : ℕ := 0x44c055fff44c0ff
def f88 : ℕ := 0x66a000000fff000
def f89 : ℕ := 0x885ccc00088fccc
def f90 : ℕ := 0x900aa0000f00ff0
def f91 : ℕ := 0x990faafffff0fff
def s23 : List ℕ := [f86,f87,f88,f89,f90,f91]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w24 : Wide 36 5 s23 := viaSearch (by decide +kernel)
def p28 : Weak 76 36 := relaxed (pick [0,1,2,3,8,9,10,11,16,17,18,19,40,41,42,43,50,51,52,53,56,57,58,59,64,65,66,67,68,69,70,71,72,73,74,75] (by decide) (by decide) (by decide))
def r31 : Rule 76 7 := cutRule 7 p28 w24
def r32 : Rule 76 7 := cutRule 7 p0 w0
def p29 : Weak 76 10 := signedPick 2 [2,3,10,11,18,19,40,42,53,59] (by decide) (by decide) (by decide)
def r33 : Rule 76 7 := cutRule 7 p29 w18
def f92 : ℕ := 0x52fff1f3
def f93 : ℕ := 0x228000e3c
def f94 : ℕ := 0x905fff90f
def f95 : ℕ := 0xd80000fc0
def s24 : List ℕ := [f92,f93,f94,f95]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w25 : Wide 24 4 s24 := viaSearch (by decide +kernel)
def p30 : Weak 76 24 := relaxed (pick [0,1,8,9,16,17,50,51,52,56,57,58,64,65,66,67,68,69,70,71,72,73,74,75] (by decide) (by decide) (by decide))
def r34 : Rule 76 7 := cutRule 7 p30 w25
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w26 : Wide 6 2 s12 := viaSearch (by decide +kernel)
def r35 : Rule 76 7 := cutRule 7 p12 w26
def r36 : Rule 76 7 := cutRule 7 p11 w26
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w27 : Wide 10 4 s17 := viaSearch (by decide +kernel)
def r37 : Rule 76 7 := cutRule 7 p17 w27
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w28 : Wide 10 4 s13 := viaSearch (by decide +kernel)
def r38 : Rule 76 7 := cutRule 7 p13 w28
def f96 : ℕ := 0x5fff00f
def s25 : List ℕ := [f96,f92,f93,f95]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w29 : Wide 24 4 s25 := viaSearch (by decide +kernel)
def r39 : Rule 76 7 := cutRule 7 p30 w29
def f97 : ℕ := 0xaa0ff0
def f98 : ℕ := 0xaf50f0
def f99 : ℕ := 0xfaaf00
def s26 : List ℕ := [f97,f98,f99]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w30 : Wide 12 3 s26 := viaSearch (by decide +kernel)
def p31 : Weak 76 12 := signedPick 4 [4,5,6,7,12,13,14,15,20,21,22,23] (by decide) (by decide) (by decide)
def r40 : Rule 76 7 := cutRule 7 p31 w30
def p32 : Weak 76 12 := signedPick 2 [2,3,6,7,10,11,14,15,18,19,22,23] (by decide) (by decide) (by decide)
def r41 : Rule 76 7 := cutRule 7 p32 w30
def f100 : ℕ := 0x28a305aacccccccc00028a30faacccccccc
def f101 : ℕ := 0x30c350ccf0f0f0f000030c3f0ccf0f0f0f0
def s27 : List ℕ := [f41,f100,f101,f38,f40,f37,f42]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b0 : Ban 76 8 s27 := viaRules (ws := [s11]) (consBan b1 (nilBan _ _))
  (dictionary [(391265303,r13),(1259231329,r13),(1538301500,r14),(442999824,r15),(2130618819,r16),(1579274016,r17),(1608298784,r18),(861741928,r16),(816869088,r19),(925149300,r20),(596411043,r20),(175711749,r21),(283991961,r16),(986801570,r16),(132650294,r22),(1520448127,r23),(1150378439,r23),(1181841799,r24),(422155985,r16),(892992145,r16),(2076284066,r25),(315649778,r26),(737320599,r16),(219300780,r16),(1159098925,r27),(1267379137,r20),(534185363,r20),(1926978540,r28),(2035258752,r16),(411070410,r16),(1332989243,r29),(573303429,r23),(1884250928,r23),(1274442080,r30),(514756266,r16),(1082652336,r18),(696750424,r31),(1637392361,r26),(1637091766,r18),(1247821448,r16),(1293557636,r13),(1763603715,r32),(1479187538,r33),(1930082592,r34),(252645024,r16),(26760829,r16),(121131118,r13),(229411330,r32),(1718317662,r20),(393907923,r15),(502188135,r35),(1665538934,r16),(1856540058,r13),(1096854244,r32),(1066160479,r33),(1794461343,r14),(1034775529,r36),(782074399,r33),(637719599,r34),(508660601,r18),(1498467313,r33),(1601674912,r34),(1472615914,r18),(843021949,r33),(167489679,r34),(407660702,r26),(1503730954,r33),(300610275,r34),(540781298,r26),(871646292,r16),(1753721308,r37),(76283740,r38),(2082644959,r20),(330598355,r39),(800644434,r16),(1942818686,r40),(2051098898,r16),(226163296,r36),(1430768978,r40),(1539049190,r20),(1738678302,r35),(2056652461,r41),(1296966647,r16),(1965572981,r35),(889116781,r41),(129430967,r20),(806518081,r36),(1339571040,r20),(1239772464,r37),(842821981,r20),(477846767,r18),(278924387,r20),(170891369,r37),(123468048,r20),(120866589,r26),(781727449,r20),(35350559,r15),(1169362172,r35),(789267059,r34),(1923278672,r20),(599790707,r33)])
  (by decide) (by decide +kernel) (by decide +kernel)
theorem cert6 : Ban 76 8 bank := b0
end PEqualNP.Outside.L_meta_14954.B1

namespace PEqualNP.Outside.L_meta_14954
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def target (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def witness : Circuit := ⟨[⟨.or,[0,7]⟩,⟨.or,[4,5]⟩,⟨.or,[6,9]⟩,⟨.and,[8,10]⟩,⟨.and,[4,5]⟩,⟨.or,[6,7]⟩,⟨.or,[1,2]⟩,⟨.and,[13,14]⟩,⟨.and,[3,6]⟩,⟨.or,[11,12]⟩,⟨.or,[15,17]⟩,⟨.or,[16,18]⟩],19⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem shaped : Monotone2 witness := by simp [witness,Monotone2]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem cost : witness.size=12 := rfl
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem valid : ∀ x,witness.eval (List.ofFn x)=target x := by decide +kernel
def inputs : List ℕ := [0x1082598015400aaaa208259800052200aaaafff8412cc00aa00ffff90412cc01069300ffff,0x51460b5599999998051460a45162999999800028a30faacccccccc028a30f269b1ccccccc,0x6186a199e1e1e1e006186a0514741e1e1e000030c3f0ccf0f0f0f0030c3f038e3e0f0f0f0,0x1ffffffffffffffffffe0000000000000000001fffffffffffffffffff0000000000000000000,0x1c8001e00aa0154401c80081f800aa0154fff00fc000f00ff00ffa00fc00c0fc00ff00ff,0x720001e00155540087200017e00015554000003f0000f000ffff0043f0000ff0000ffff00,0x20000000000000000000c800001aaa894000001000c00000ffff0000007c00000ffffff000000,0x18c3154000000000030c3154000000000000000ffffff00000000007ffffff000000000000]
def v : ℕ := 0x1ffffffffffffffffffe0000000000000000001fffffffffffffffffff0000000000000000000
def bank0 : List ℕ := [0x10412cc00029100555590412cc01069300ffff,0x28a305228b14cccccc028a30f269b1ccccccc,0x30c35028a3a0f0f0f0030c3f038e3e0f0f0f0,0x200e40040fc005500aaa00fc00c0fc00ff00ff,0x4390000bf0000aaaa0043f0000ff0000ffff00,0x6400000d5544a0000007c00000ffffff000000,0x18618aa0000000000007ffffff000000000000]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem wide0 : Wide 76 8 bank0 := widen (by decide +kernel) B0.cert6
def rr0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75]
def ix0 := rr0 ++ rr0.map (153+·)
def base0 : ℕ := 228
def pr0 : Weak 153 76 := signedPick base0 rr0 (by decide) (by decide) (by decide)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem images0 : ∀ a∈inputs, pr0.f a=0 ∨ pr0.f a∈bank0 := by decide +kernel
def bank1 : List ℕ := [0x8412cc00aa005555fff8412cc00aa00ffff,0x28a305aacccccccc00028a30faacccccccc,0x30c350ccf0f0f0f000030c3f0ccf0f0f0f0,0xe4000f005500aafff00fc000f00ff00ff,0x390000f000aaaa000003f0000f000ffff00,0xc00000ffff000000,0xc618aa0000000000000ffffff0000000000]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem wide1 : Wide 76 8 bank1 := widen (by decide +kernel) B1.cert6
def rr1 : List ℕ := [76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151]
def ix1 := rr1 ++ rr1.map (153+·)
def base1 : ℕ := 304
def pr1 : Weak 153 76 := signedPick base1 rr1 (by decide) (by decide) (by decide)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem images1 : ∀ a∈inputs, pr1.f a=0 ∨ pr1.f a∈bank1 := by decide +kernel
def posBits : ℕ := 0x48191919191919191919191919c9c8aeacaaa9a8a89e9c9a9998988f8e8d8d8c8c8b8b8a8a6e6c6a685e5c5a584f4e4d4c4b4a49483e3e3c3c3a3a38382f2f2d2d2b2b29291f1f1d1d1b1b191911e0d0c1c0c0a6a4a2a1a0a096949291909087868585848483838282707066646462626156545452525147464544444342424141363634343232303027272525232321211717151513131111
def negBits : ℕ := 0x4008080808080808080808080889882e2c2a8988281e1c1a8988180f0e890d880c890b880a2e2c2a281e1c1a180f0e0d0c0b0a09082e1e2c1c2a1a28182e0f2c0d2a0b28091e0f1c0d1a0b180900605081804026242281802016141281801007068105800481038002605026602460226016501450125007060540040340024001261624142212201026072405220320011607140512031001
def sample (bank : ℕ) (i : Fin 153) (j : Fin 8) := bank.testBit (8*i.val+j.val)

def seeds : List Wire := inputs.map (fun a => (false,a))
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem listed : ∀ i : Fin 153, seeds.map (read i.val)=List.ofFn (sample posBits i) ∧
    seeds.map (read (153+i.val))=List.ofFn (sample negBits i) := by decide +kernel
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem labels : ∀ i : Fin 153, target (sample posBits i)=true ∧ target (sample negBits i)=false := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem essential : ∀ a∈inputs, ∃ i : Fin 153, ∀ b∈inputs, b.testBit i.val≠b.testBit (153+i.val) → b=a := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem initial {k S} (live : Live 153 k S) (sub : ∀ a∈S,a∈inputs) : S=inputs.toFinset := by
  apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
  intro a ha
  obtain ⟨i,h⟩ := essential a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
  exact h b (sub b hb) sep ▸ hb
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem trace (C : Circuit) (fan : FanInTwo C) (eq : circuitFun 8 C=target) :
    ∃ k≤C.gates.countP counted, Live 153 k inputs.toFinset := by
  let final := execute C.gates seeds
  let out := final.getD C.output zero
  have ev (i : ℕ) : read i out = C.eval (seeds.map (read i)) := by
    rw [show read i out = (final.map (read i)).getD C.output false from (read_get i final C.output).symm]
    rw [show final=execute C.gates seeds from rfl,execute_read i _ _ fan];rfl
  have result (x : Fin 8 → Bool) : C.eval (List.ofFn x)=target x := congrFun eq x
  have good : Good 153 out.2 := by
    intro i hi same
    let j : Fin 153 := ⟨i,hi⟩
    have diff : read i out=read (153+i) out := by simp [read,same]
    have p := ev i;have n := ev (153+i)
    rw [(listed j).1,result,(labels j).1] at p
    rw [(listed j).2,result,(labels j).2] at n
    rw [p,n] at diff;contradiction
  have nz : out.2≠0 := by
    intro z;have bad := good 0 (by decide);simp [z] at bad
  have found : out.2∈ reps final := (get_simple final C.output).resolve_left nz
  obtain ⟨k,S,limit,live,sub⟩ := extract good nz C.gates seeds found
  have stays : ∀ a∈S, a∈inputs := by simpa [reps,seeds,List.map_map,Function.comp_def] using sub
  exact ⟨k,limit,initial live stays ▸ live⟩


def pr : Bool → Weak 153 76 | false => pr0 | true => pr1
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem killed (d a b : ℕ) (hd : d<4) (hit : v=a ∨ v=b) :
    ∃ t, (pr t).f (combine d a b)=0 := by
  rcases hit with rfl|rfl
  · obtain ⟨s,c,h⟩ := forced d hd true
    cases s with
    | false => exact ⟨false,forcedLeft (is:=ix0) (s:=false) (c:=c) hd (by decide) (by decide) (by simpa using h)⟩
    | true => exact ⟨true,forcedLeft (is:=ix1) (s:=true) (c:=c) hd (by decide) (by decide) (by simpa using h)⟩
  · obtain ⟨s,c,h⟩ := forced d hd false
    cases s with
    | false => exact ⟨false,forcedRight (is:=ix0) (s:=false) (c:=c) hd (by decide) (by decide) (by simpa using h)⟩
    | true => exact ⟨true,forcedRight (is:=ix1) (s:=true) (c:=c) hd (by decide) (by decide) (by simpa using h)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem eleven {k : ℕ} (live : Live 153 k inputs.toFinset) : 11≤k := by
  obtain ⟨t,j,T,lim,ok,sub⟩ := doubleElim pr v killed (by decide +kernel) live (by decide)
  by_contra! small
  have project {w : List ℕ} (im : ∀ a∈inputs, (pr t).f a=0 ∨ (pr t).f a∈w) : Possible 76 8 w := by
    refine ⟨j,T,by omega,ok,?_⟩
    intro x hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp (sub x hx)
    exact (im _ (List.mem_toFinset.mp ha)).resolve_left (liveNonzero ok _ hx)
  cases t
  · exact wide0 (project images0)
  · exact wide1 (project images1)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem counted_lt {gs : List Gate} (h : ∃ g ∈ gs, g.op = .not) : gs.countP counted < gs.length := by
  apply Nat.lt_of_le_of_ne List.countP_le_length
  intro eq
  obtain ⟨g,hg,hop⟩ := h
  have bad := List.countP_eq_length.mp eq g hg
  simp [counted,hop] at bad

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem noSaving (s : ℕ) (h : HasCircuitSize 8 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x,C.eval (List.ofFn x)=target x := by
  obtain ⟨C,fan,hsize,ev⟩ := h
  by_cases used : ∃ g∈C.gates, g.op=.not
  · obtain ⟨k,lim,ok⟩ := trace C fan (funext ev)
    have lb := eleven ok
    have strict := counted_lt used
    change C.gates.length ≤ s at hsize
    refine ⟨witness,shaped,?_,valid⟩
    rw [cost]; omega
  · refine ⟨C,?_,hsize,ev⟩
    intro g hg
    rcases (fan g hg).1 with a|b|n
    · exact ⟨Or.inl a,(fan g hg).2⟩
    · exact ⟨Or.inr b,(fan g hg).2⟩
    · exact False.elim (used ⟨g,hg,n⟩)
end PEqualNP.Outside.L_meta_14954

theorem PEqualNP.Outside.L_meta_14954 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fan _ ev
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gates,o⟩
  obtain ⟨D, shaped, cost, valid⟩ := PEqualNP.Outside.L_meta_14954.noSaving gates.length ⟨C,fan,le_rfl,ev⟩
  exact ⟨D.gates,D.output,shaped,cost,valid⟩
