import PEqualNP.Defs

-- The signed live-wire calculus follows L-meta-10532 and L-meta-12325.

namespace PEqualNP.Outside.L_meta_14582

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

end PEqualNP.Outside.L_meta_14582

namespace PEqualNP.Outside.L_meta_14582

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

end PEqualNP.Outside.L_meta_14582

namespace PEqualNP.Outside.L_meta_14582
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







end PEqualNP.Outside.L_meta_14582

namespace PEqualNP.Outside.L_meta_14582

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
end PEqualNP.Outside.L_meta_14582

namespace PEqualNP.Outside.L_meta_14582

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
end PEqualNP.Outside.L_meta_14582

namespace PEqualNP.Outside.L_meta_14582
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

end PEqualNP.Outside.L_meta_14582

namespace PEqualNP.Outside.L_meta_14582

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
end PEqualNP.Outside.L_meta_14582

namespace PEqualNP.Outside.L_meta_14582.B0
def bank : List ℕ := [0x3823982083f4280023e0020256035b1a0441c9e0ae70830fd0a4008f88488bf80f6c6813672,0x2863902c2386501256540a8131030c672564a8a98e49b09e19406959522b14c54cb39c9d92a,0x6a10ad95412e0a3464cc227806c3585c274721b842b65504ba38d1933489e01f0d61729d1cc,0x94dcffc07c7eda0c07c21aa844aa33a1303a425373ff01f1fb68b01f086aa11aa8ce86c0e9,0xf3089fa6126d6f54a7af0399001f24a92210ebcc227e9849b5bd52bebd0e64007c92a488c3a,0x42986480540900c9000021780850a0000212010a61b231713c4364cd009fe561738859494a0,0x402420800850088039004802c0080d00810c0d50b0eeca39c86207ee41a10b85223d4306,0x40000000800000218004c042120000088a802371ac4c82244231b728130708e84258622ad9]
def f0 : ℕ := 0x2b900ff2
def f1 : ℕ := 0x9c8b1b916
def f2 : ℕ := 0x12c42258dc
def f3 : ℕ := 0x241046b708
def f4 : ℕ := 0x3ffffabfd8
def s0 : List ℕ := [f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w0 : Wide 19 4 s0 := viaSearch (by decide +kernel)
def p0 : Weak 150 19 := signedPick 0 [0,6,7,18,26,30,31,37,48,53,55,59,67,91,93,101,122,132,136] (by decide) (by decide) (by decide)
def r0 : Rule 150 8 := cutRule 8 p0 w0
def f5 : ℕ := 0x2110d2e590f
def f6 : ℕ := 0x528b205bbb2
def f7 : ℕ := 0x380272b802fb
def f8 : ℕ := 0x70c20073e614
def f9 : ℕ := 0x822d88d22de8
def s1 : List ℕ := [f5,f6,f7,f8,f9]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w1 : Wide 24 5 s1 := viaSearch (by decide +kernel)
def p1 : Weak 150 24 := relaxed (pick [2,8,20,21,24,28,45,46,56,60,64,65,69,82,86,89,98,113,115,118,131,138,141,144] (by decide) (by decide) (by decide))
def r1 : Rule 150 8 := cutRule 8 p1 w1
def f10 : ℕ := 0x360bea
def f11 : ℕ := 0x49a5da
def f12 : ℕ := 0x6c16d5
def f13 : ℕ := 0x81ce3d
def s2 : List ℕ := [f10,f11,f12,f13]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w2 : Wide 12 3 s2 := viaSearch (by decide +kernel)
def p2 : Weak 150 12 := relaxed (pick [0,2,17,21,43,45,91,101,118,122,136,144] (by decide) (by decide) (by decide))
def r2 : Rule 150 8 := cutRule 8 p2 w2
def f14 : ℕ := 0x24db04db6
def f15 : ℕ := 0x891913a3a
def f16 : ℕ := 0x142043856c
def f17 : ℕ := 0x214624b8d4
def f18 : ℕ := 0x3ffff9bd7c
def s3 : List ℕ := [f14,f15,f16,f17,f18]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w3 : Wide 19 4 s3 := viaSearch (by decide +kernel)
def p3 : Weak 150 19 := signedPick 0 [0,7,14,18,44,67,74,84,91,93,101,103,112,121,122,124,132,136,140] (by decide) (by decide) (by decide)
def r3 : Rule 150 8 := cutRule 8 p3 w3
def f19 : ℕ := 0x260ba
def f20 : ℕ := 0x509c6
def f21 : ℕ := 0x89274
def f22 : ℕ := 0xffcf6
def s4 : List ℕ := [f19,f20,f21,f22]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w4 : Wide 10 3 s4 := viaSearch (by decide +kernel)
def p4 : Weak 150 10 := signedPick 0 [0,18,74,93,112,121,124,132,136,140] (by decide) (by decide) (by decide)
def r4 : Rule 150 8 := cutRule 8 p4 w4
def f23 : ℕ := 0x10642ae2e85
def f24 : ℕ := 0x109d1d313a3
def f25 : ℕ := 0x1a491834dab0
def f26 : ℕ := 0x1c802839047b
def f27 : ℕ := 0x20300442f15c
def s5 : List ℕ := [f23,f24,f25,f26,f27]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w5 : Wide 23 4 s5 := viaSearch (by decide +kernel)
def p5 : Weak 150 23 := relaxed (pick [9,13,20,49,50,51,52,56,64,65,66,69,82,86,89,98,106,113,115,117,135,139,141] (by decide) (by decide) (by decide))
def r5 : Rule 150 8 := cutRule 8 p5 w5
def f28 : ℕ := 0x1307c
def f29 : ℕ := 0x6419a
def f30 : ℕ := 0x88b62
def f31 : ℕ := 0xffd7a
def s6 : List ℕ := [f28,f29,f30,f31]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w6 : Wide 10 3 s6 := viaSearch (by decide +kernel)
def p6 : Weak 150 10 := signedPick 0 [0,18,30,31,37,53,55,93,132,136] (by decide) (by decide) (by decide)
def r6 : Rule 150 8 := cutRule 8 p6 w6
def f32 : ℕ := 0x340f8
def f33 : ℕ := 0x4298e
def f34 : ℕ := 0xf6bc8
def f35 : ℕ := 0xffcbe
def s7 : List ℕ := [f32,f33,f34,f35]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w7 : Wide 10 3 s7 := viaSearch (by decide +kernel)
def p7 : Weak 150 10 := signedPick 22 [22,29,32,40,42,54,92,114,119,149] (by decide) (by decide) (by decide)
def r7 : Rule 150 8 := cutRule 8 p7 w7
def f36 : ℕ := 0x401a1f834
def f37 : ℕ := 0x11da423b58
def f38 : ℕ := 0x12a052558e
def f39 : ℕ := 0x36f1f4de1c
def f40 : ℕ := 0x3ffffb79b6
def s8 : List ℕ := [f36,f37,f38,f39,f40]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w8 : Wide 19 4 s8 := viaSearch (by decide +kernel)
def p8 : Weak 150 19 := signedPick 4 [4,10,40,58,70,71,77,78,83,88,92,95,105,107,114,119,146,148,149] (by decide) (by decide) (by decide)
def r8 : Rule 150 8 := cutRule 8 p8 w8
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w9 : Wide 23 5 s5 := viaSearch (by decide +kernel)
def r9 : Rule 150 8 := cutRule 8 p5 w9
def f41 : ℕ := 0x18876
def f42 : ℕ := 0x231cc
def f43 : ℕ := 0xbbae4
def f44 : ℕ := 0xffd5e
def s9 : List ℕ := [f41,f42,f43,f44]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w10 : Wide 10 3 s9 := viaSearch (by decide +kernel)
def p9 : Weak 150 10 := signedPick 4 [4,10,40,71,78,92,114,119,146,149] (by decide) (by decide) (by decide)
def r10 : Rule 150 8 := cutRule 8 p9 w10
def f45 : ℕ := 0x50550e0fa
def f46 : ℕ := 0x1060829f90
def f47 : ℕ := 0x31e6e634dc
def f48 : ℕ := 0x3d75d5aeb0
def f49 : ℕ := 0x3ffffadbda
def s10 : List ℕ := [f45,f46,f47,f48,f49]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w11 : Wide 19 4 s10 := viaSearch (by decide +kernel)
def p10 : Weak 150 19 := signedPick 3 [3,15,27,35,41,57,61,62,72,73,85,96,100,102,120,125,126,127,142] (by decide) (by decide) (by decide)
def r11 : Rule 150 8 := cutRule 8 p10 w11
def f50 : ℕ := 0x31e71
def f51 : ℕ := 0xc21cf
def f52 : ℕ := 0xb04ba4
def f53 : ℕ := 0xc0cc1e
def s11 : List ℕ := [f50,f51,f52,f53]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w12 : Wide 12 4 s11 := viaSearch (by decide +kernel)
def p11 : Weak 150 12 := relaxed (pick [20,49,50,52,66,69,86,89,98,115,117,139] (by decide) (by decide) (by decide))
def r12 : Rule 150 7 := cutRule 7 p11 w12
def f54 : ℕ := 0x25e67
def f55 : ℕ := 0x30a3ba
def f56 : ℕ := 0x8d09dc
def f57 : ℕ := 0xc1ac1b
def s12 : List ℕ := [f54,f55,f56,f57]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w13 : Wide 12 3 s12 := viaSearch (by decide +kernel)
def p12 : Weak 150 12 := relaxed (pick [2,8,20,24,60,69,86,89,98,115,118,138] (by decide) (by decide) (by decide))
def r13 : Rule 150 7 := cutRule 7 p12 w13
def f58 : ℕ := 0x43ec7
def f59 : ℕ := 0x22c37c
def f60 : ℕ := 0x9909ba
def f61 : ℕ := 0xd0cd0d
def s13 : List ℕ := [f58,f59,f60,f61]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w14 : Wide 12 3 s13 := viaSearch (by decide +kernel)
def p13 : Weak 150 12 := relaxed (pick [2,20,34,36,49,52,66,86,116,117,118,138] (by decide) (by decide) (by decide))
def r14 : Rule 150 7 := cutRule 7 p13 w14
def f62 : ℕ := 0xe7
def f63 : ℕ := 0x31d
def f64 : ℕ := 0xc3a
def s14 : List ℕ := [f62,f63,f64]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w15 : Wide 6 2 s14 := viaSearch (by decide +kernel)
def p14 : Weak 150 6 := relaxed (pick [20,69,86,89,98,115] (by decide) (by decide) (by decide))
def r15 : Rule 150 7 := cutRule 7 p14 w15
def r16 : Rule 150 7 := cutRule 7 p1 w1
def f65 : ℕ := 0x3003a0
def s15 : List ℕ := [f50,f51,f65,f53]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w16 : Wide 12 4 s15 := viaSearch (by decide +kernel)
def r17 : Rule 150 7 := cutRule 7 p11 w16
def f66 : ℕ := 0x1457c7
def f67 : ℕ := 0x2aa3ea
def f68 : ℕ := 0x41ac3f
def f69 : ℕ := 0x8e48fc
def s16 : List ℕ := [f66,f67,f68,f69]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w17 : Wide 12 3 s16 := viaSearch (by decide +kernel)
def p15 : Weak 150 12 := relaxed (pick [2,8,21,28,45,46,56,65,69,115,118,144] (by decide) (by decide) (by decide))
def r18 : Rule 150 7 := cutRule 7 p15 w17
def f70 : ℕ := 0x1f7ab3b3ef76f6
def f71 : ℕ := 0x355c28960b0112
def f72 : ℕ := 0x355c2896bb857e
def f73 : ℕ := 0x3f7efbf2a49f7e
def f74 : ℕ := 0x3ffffffdfbe4ec
def s17 : List ℕ := [f70,f71,f72,f73,f74]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w18 : Wide 27 4 s17 := viaSearch (by decide +kernel)
def p16 : Weak 150 27 := signedPick 9 [9,10,18,20,37,40,41,43,49,53,62,66,71,81,85,86,92,93,94,102,113,114,119,132,136,137,141] (by decide) (by decide) (by decide)
def r19 : Rule 150 7 := cutRule 7 p16 w18
def f75 : ℕ := 0xc82d8
def f76 : ℕ := 0xb04304
def f77 : ℕ := 0xb04fa4
def f78 : ℕ := 0xbeeaae
def f79 : ℕ := 0xfffff0
def s18 : List ℕ := [f75,f76,f77,f78,f79]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w19 : Wide 12 4 s18 := viaSearch (by decide +kernel)
def p17 : Weak 150 12 := signedPick 9 [9,13,49,51,56,64,65,82,86,89,113,141] (by decide) (by decide) (by decide)
def r20 : Rule 150 7 := cutRule 7 p17 w19
def f80 : ℕ := 0x1f49f
def f81 : ℕ := 0x69b79
def f82 : ℕ := 0xd14d5c
def f83 : ℕ := 0xe80ea7
def s19 : List ℕ := [f80,f81,f82,f83]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w20 : Wide 12 3 s19 := viaSearch (by decide +kernel)
def p18 : Weak 150 12 := relaxed (pick [9,13,51,56,65,66,69,106,115,117,135,139] (by decide) (by decide) (by decide))
def r21 : Rule 150 7 := cutRule 7 p18 w20
def f84 : ℕ := 0x279
def f85 : ℕ := 0x497
def f86 : ℕ := 0x92e
def s20 : List ℕ := [f84,f85,f86]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w21 : Wide 6 2 s20 := viaSearch (by decide +kernel)
def p19 : Weak 150 6 := relaxed (pick [20,49,52,66,86,117] (by decide) (by decide) (by decide))
def r22 : Rule 150 7 := cutRule 7 p19 w21
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w22 : Wide 6 3 s14 := viaSearch (by decide +kernel)
def r23 : Rule 150 7 := cutRule 7 p14 w22
def f87 : ℕ := 0x20c400314cd8b9008e7
def f88 : ℕ := 0x28492191ca8a136b6472a
def f89 : ℕ := 0x291002a70a0a6410f9c3c
def f90 : ℕ := 0x5486084000152bc6b1148
def f91 : ℕ := 0x5686086fcab5abc6bffeb
def f92 : ℕ := 0x8021351025330c4d4e694
def s21 : List ℕ := [f87,f88,f89,f90,f91,f92]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w23 : Wide 42 6 s21 := viaSearch (by decide +kernel)
def p20 : Weak 150 42 := relaxed (pick [2,8,9,12,13,16,20,21,24,28,33,34,36,45,46,47,49,50,51,52,56,60,64,65,66,69,82,86,89,98,106,113,115,116,117,118,131,135,138,139,141,144] (by decide) (by decide) (by decide))
def r24 : Rule 150 7 := cutRule 7 p20 w23
def f93 : ℕ := 0x20c42b2c5c85
def f94 : ℕ := 0x21351cc626a3
def f95 : ℕ := 0x1449218289b5b0
def f96 : ℕ := 0x15100282b2087b
def f97 : ℕ := 0x2a86084555e35c
def s22 : List ℕ := [f93,f94,f95,f96,f97]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w24 : Wide 27 5 s22 := viaSearch (by decide +kernel)
def p21 : Weak 150 27 := relaxed (pick [9,13,20,49,50,51,52,56,60,64,65,66,69,82,86,89,98,106,113,115,116,117,131,135,138,139,141] (by decide) (by decide) (by decide))
def r25 : Rule 150 7 := cutRule 7 p21 w24
def f98 : ℕ := 0x13266bbbe66
def f99 : ℕ := 0x6888916cc9ff
def f100 : ℕ := 0x964508d77799
def s23 : List ℕ := [f98,f99,f100]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w25 : Wide 24 3 s23 := viaSearch (by decide +kernel)
def p22 : Weak 150 24 := relaxed (pick [10,18,20,31,37,40,41,49,52,53,55,62,66,71,78,86,94,99,108,114,117,132,137,146] (by decide) (by decide) (by decide))
def r26 : Rule 150 7 := cutRule 7 p22 w25
def f101 : ℕ := 0x13611ddce
def f102 : ℕ := 0x736dd8c06
def f103 : ℕ := 0x9ff3051c8
def s24 : List ℕ := [f101,f102,f103]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w26 : Wide 18 3 s24 := viaSearch (by decide +kernel)
def p23 : Weak 150 18 := signedPick 18 [18,29,32,35,40,41,42,54,61,62,74,100,112,114,121,124,127,132] (by decide) (by decide) (by decide)
def r27 : Rule 150 7 := cutRule 7 p23 w26
def f104 : ℕ := 0x1460c2198229d1e6bf5e
def f105 : ℕ := 0x17e5cf7fd60fc9969da8
def f106 : ℕ := 0x376bd6bfb66896ad6e4c
def f107 : ℕ := 0x3cfefbd9eba15162b356
def s25 : List ℕ := [f104,f105,f106,f107]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w27 : Wide 39 4 s25 := viaSearch (by decide +kernel)
def p24 : Weak 150 39 := signedPick 1 [1,5,10,18,23,29,31,32,35,37,40,41,42,49,53,54,55,61,62,71,74,78,79,86,89,94,99,100,108,111,112,114,121,124,127,132,134,137,146] (by decide) (by decide) (by decide)
def r28 : Rule 150 7 := cutRule 7 p24 w27
def f108 : ℕ := 0x200c404a7c05d809
def f109 : ℕ := 0x2013502c85b26a05
def f110 : ℕ := 0x1482121802924b4b50
def f111 : ℕ := 0x1508002803a10087a7
def f112 : ℕ := 0x2a55e087954efe35fa
def s26 : List ℕ := [f108,f109,f110,f111,f112]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w28 : Wide 35 5 s26 := viaSearch (by decide +kernel)
def p25 : Weak 150 35 := relaxed (pick [9,10,13,20,35,37,42,49,50,51,52,56,62,64,65,66,69,82,86,89,92,93,98,102,106,112,113,114,115,117,132,135,137,139,141] (by decide) (by decide) (by decide))
def r29 : Rule 150 7 := cutRule 7 p25 w28
def f113 : ℕ := 0x517
def f114 : ℕ := 0x8ae
def s27 : List ℕ := [f84,f113,f114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w29 : Wide 6 3 s27 := viaSearch (by decide +kernel)
def p26 : Weak 150 6 := relaxed (pick [13,49,52,64,106,141] (by decide) (by decide) (by decide))
def r30 : Rule 150 7 := cutRule 7 p26 w29
def f115 : ℕ := 0x29cadbf2
def f116 : ℕ := 0x72decc132
def f117 : ℕ := 0x8fbda1ac0
def s28 : List ℕ := [f115,f116,f117]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w30 : Wide 18 3 s28 := viaSearch (by decide +kernel)
def p27 : Weak 150 18 := signedPick 10 [10,18,31,37,40,41,53,55,62,71,78,94,99,108,114,132,137,146] (by decide) (by decide) (by decide)
def r31 : Rule 150 7 := cutRule 7 p27 w30
def f118 : ℕ := 0x402420800850088039004802c0080d00810c0d50b0eeca39c86207ee41a10b85223d4306
def f119 : ℕ := 0x40000000800000218004c042120000088a802371ac4c82244231b728130708e84258622ad9
def f120 : ℕ := 0x2863902c2386501256540a8131030c672564a8a98e49b09e19406959522b14c54cb39c9d92a
def f121 : ℕ := 0x3823982083f4280023e0020256035b1a0441c9e0ae70830fd0a4008f88488bf80f6c6813672
def f122 : ℕ := 0x42986480540900c9000021780850a0000212010a61b231713c4364cd009fe561738859494a0
def f123 : ℕ := 0x6a10ad95412e0a3464cc227806c3585c274721b842b65504ba38d1933489e01f0d61729d1cc
def f124 : ℕ := 0xfb4ddffe17efeff4e7ff23bb845fa7bb3313efed377ff85fbfbfdbbffd8eee11fe9eececcfb
def s29 : List ℕ := [f118,f119,f120,f121,f122,f123,f124]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b1 : Ban 150 8 s29 := viaRules (ws := []) (nilBan _ _)
  (dictionary [(356987756,r12),(749829677,r13),(1721360282,r14),(2036493436,r14),(204688055,r13),(950245061,r13),(1161305115,r13),(1122908477,r15),(803524429,r13),(1928819027,r13),(613040254,r13),(1864972866,r16),(994976000,r13),(1368947856,r17),(1936695109,r18),(1233177972,r19),(1029588861,r18),(314648486,r13),(1741106581,r20),(783375095,r18),(511019227,r18),(148025618,r13),(1284480453,r18),(262275613,r18),(1433493571,r13),(1638566308,r21),(1101169613,r13),(1368287984,r22),(1579330832,r14),(790312878,r13),(1397573521,r23),(27231574,r15),(1658934333,r16),(755057823,r13),(1621071447,r24),(250729500,r21),(1608820118,r25),(238478171,r21),(1578540748,r26),(1659924713,r13),(2068957748,r26),(1289157874,r13),(895763515,r13),(1231361603,r23),(857464939,r27),(646073463,r13),(834833185,r28),(1458829852,r29),(1713706285,r30),(405254962,r31)])
  (by decide) (by decide +kernel) (by decide +kernel)
def f125 : ℕ := 0x3282991b436e
def f126 : ℕ := 0xc429446f3cae
def f127 : ℕ := 0x109d498a4fe4c
def f128 : ℕ := 0x1e6c012f3e099
def f129 : ℕ := 0x2011d61d0cff1
def s30 : List ℕ := [f125,f126,f127,f128,f129]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w31 : Wide 25 4 s30 := viaSearch (by decide +kernel)
def p28 : Weak 150 25 := relaxed (pick [0,2,8,14,17,21,28,43,45,46,56,65,69,74,84,87,91,101,115,118,122,124,136,140,144] (by decide) (by decide) (by decide))
def r32 : Rule 150 8 := cutRule 8 p28 w31
def r33 : Rule 150 8 := cutRule 8 p20 w23
def f130 : ℕ := 0x2ea3f
def f131 : ℕ := 0x6907d6
def f132 : ℕ := 0x8d18f9
def f133 : ℕ := 0x962de2
def s31 : List ℕ := [f130,f131,f132,f133]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w32 : Wide 12 3 s31 := viaSearch (by decide +kernel)
def p29 : Weak 150 12 := relaxed (pick [0,9,13,17,30,43,53,55,66,106,117,136] (by decide) (by decide) (by decide))
def r34 : Rule 150 8 := cutRule 8 p29 w32
def r35 : Rule 150 8 := cutRule 8 p21 w24
def f134 : ℕ := 0x9090042270874e493c89da
def f135 : ℕ := 0x12a22224d8724a8c889771e
def f136 : ℕ := 0x20528b911860855a6f5d618
def f137 : ℕ := 0x560454244011593b54b12c4
def f138 : ℕ := 0x7fc776a44155ff3ffeb1af5
def f139 : ℕ := 0x8008091b2483aa212c6ed25
def s32 : List ℕ := [f134,f135,f136,f137,f138,f139]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w33 : Wide 46 6 s32 := viaSearch (by decide +kernel)
def p30 : Weak 150 46 := relaxed (pick [0,2,7,8,14,17,18,20,21,24,28,43,44,45,46,56,60,64,65,67,69,74,82,84,86,87,89,91,93,98,101,103,112,113,115,118,121,122,124,131,132,136,138,140,141,144] (by decide) (by decide) (by decide))
def r36 : Rule 150 8 := cutRule 8 p30 w33
def r37 : Rule 150 8 := cutRule 8 p15 w17
def f140 : ℕ := 0x80c82af05d05
def f141 : ℕ := 0x813a1d152743
def f142 : ℕ := 0x191123032ab560
def f143 : ℕ := 0x1a2005034408fb
def f144 : ℕ := 0x244e00c49be2bc
def s33 : List ℕ := [f140,f141,f142,f143,f144]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w34 : Wide 27 5 s33 := viaSearch (by decide +kernel)
def p31 : Weak 150 27 := relaxed (pick [9,13,20,37,49,50,51,52,56,64,65,66,69,82,86,89,93,98,106,112,113,115,117,132,135,139,141] (by decide) (by decide) (by decide))
def r38 : Rule 150 8 := cutRule 8 p31 w34
def f145 : ℕ := 0x89144317388226555d7ce
def f146 : ℕ := 0x2200b0428c42fd0ad10e3b
def f147 : ℕ := 0x2d1544188629b45518661ab
def f148 : ℕ := 0x3c52a0184000f1eec0e9890
def f149 : ℕ := 0x402018e50093588973b6164
def f150 : ℕ := 0xbe57e61a7922f9fffae9edc
def s34 : List ℕ := [f145,f146,f147,f148,f149,f150]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w35 : Wide 46 6 s34 := viaSearch (by decide +kernel)
def p32 : Weak 150 46 := relaxed (pick [2,8,11,19,20,21,22,24,28,29,32,40,42,45,46,54,56,58,60,64,65,68,69,70,80,81,82,86,88,89,90,92,95,98,105,113,114,115,118,119,131,138,141,143,144,149] (by decide) (by decide) (by decide))
def r39 : Rule 150 8 := cutRule 8 p32 w35
def f151 : ℕ := 0x81904af0ba09
def f152 : ℕ := 0x82742d1a4e85
def f153 : ℕ := 0x1a224603456ad0
def f154 : ℕ := 0x1c400a038811e7
def f155 : ℕ := 0x211c019437c57a
def s35 : List ℕ := [f151,f152,f153,f154,f155]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w36 : Wide 27 5 s35 := viaSearch (by decide +kernel)
def p33 : Weak 150 27 := relaxed (pick [9,10,13,20,42,49,50,51,52,56,64,65,66,69,82,86,89,92,98,106,113,114,115,117,135,139,141] (by decide) (by decide) (by decide))
def r40 : Rule 150 8 := cutRule 8 p33 w36
def f156 : ℕ := 0x1ec5f
def f157 : ℕ := 0x6987b8
def f158 : ℕ := 0x741753
def f159 : ℕ := 0x960bec
def s36 : List ℕ := [f156,f157,f158,f159]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w37 : Wide 12 3 s36 := viaSearch (by decide +kernel)
def p34 : Weak 150 12 := relaxed (pick [0,17,64,82,87,89,93,98,112,121,140,141] (by decide) (by decide) (by decide))
def r41 : Rule 150 8 := cutRule 8 p34 w37
def f160 : ℕ := 0x3a06e6ba17
def f161 : ℕ := 0x2605382607fa
def f162 : ℕ := 0x5c80795ca07d
def f163 : ℕ := 0x7533087d7308
def f164 : ℕ := 0x88c0c099dde8
def s37 : List ℕ := [f160,f161,f162,f163,f164]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w38 : Wide 24 4 s37 := viaSearch (by decide +kernel)
def p35 : Weak 150 24 := relaxed (pick [0,13,17,23,30,31,37,49,50,51,52,64,82,87,89,93,98,106,109,112,121,135,140,141] (by decide) (by decide) (by decide))
def r42 : Rule 150 8 := cutRule 8 p35 w38
def f165 : ℕ := 0x106f0f
def f166 : ℕ := 0x23923d
def f167 : ℕ := 0x4984fa
def f168 : ℕ := 0xa60bf0
def s38 : List ℕ := [f165,f166,f167,f168]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w39 : Wide 12 3 s38 := viaSearch (by decide +kernel)
def p36 : Weak 150 12 := relaxed (pick [0,13,17,30,31,37,49,52,64,93,106,141] (by decide) (by decide) (by decide))
def r43 : Rule 150 8 := cutRule 8 p36 w39
def f169 : ℕ := 0x20f44
def f170 : ℕ := 0x80525540a6
def f171 : ℕ := 0xc6b2518d6ca
def f172 : ℕ := 0x2cf5fed96bdc
def f173 : ℕ := 0x373aa1464542
def f174 : ℕ := 0x373aa16f755a
def s39 : List ℕ := [f169,f170,f171,f172,f173,f174]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w40 : Wide 23 5 s39 := viaSearch (by decide +kernel)
def p37 : Weak 150 23 := signedPick 2 [2,7,9,18,20,21,37,43,49,53,59,66,67,86,93,101,113,116,131,132,136,138,141] (by decide) (by decide) (by decide)
def r44 : Rule 150 8 := cutRule 8 p37 w40
def r45 : Rule 150 8 := cutRule 8 p12 w13
def f175 : ℕ := 0x1808fa705b
def f176 : ℕ := 0x12648025cfb4
def f177 : ℕ := 0x1a04773408ef
def f178 : ℕ := 0x21811743aa2e
def f179 : ℕ := 0x2403664c17cc
def s40 : List ℕ := [f175,f176,f177,f178,f179]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w41 : Wide 23 4 s40 := viaSearch (by decide +kernel)
def p38 : Weak 150 23 := relaxed (pick [2,8,12,16,20,24,34,36,49,50,52,60,66,69,86,89,98,115,116,117,118,138,139] (by decide) (by decide) (by decide))
def r46 : Rule 150 8 := cutRule 8 p38 w41
def r47 : Rule 150 8 := cutRule 8 p13 w14
def f180 : ℕ := 0x66f66
def f181 : ℕ := 0x30939f
def f182 : ℕ := 0xac5ac5
def f183 : ℕ := 0xc90cf9
def s41 : List ℕ := [f180,f181,f182,f183]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w42 : Wide 12 3 s41 := viaSearch (by decide +kernel)
def p39 : Weak 150 12 := relaxed (pick [10,20,40,49,52,66,71,78,86,114,117,146] (by decide) (by decide) (by decide))
def r48 : Rule 150 8 := cutRule 8 p39 w42
def f184 : ℕ := 0x1047101d0288e203
def f185 : ℕ := 0x11019406aee17b80d
def f186 : ℕ := 0x1c4400a98388811ff3
def f187 : ℕ := 0x1ca2641883b56ea310
def f188 : ℕ := 0x2209800604537845fc
def s42 : List ℕ := [f184,f185,f186,f187,f188]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w43 : Wide 35 5 s42 := viaSearch (by decide +kernel)
def p40 : Weak 150 35 := relaxed (pick [9,13,18,20,23,31,37,49,50,51,52,53,55,56,64,65,66,69,74,82,86,89,98,106,112,113,115,117,121,124,132,134,135,139,141] (by decide) (by decide) (by decide))
def r49 : Rule 150 8 := cutRule 8 p40 w43
def f189 : ℕ := 0x100d03f63f03
def f190 : ℕ := 0x21603029e0ff
def f191 : ℕ := 0xc402ccc407fc
def f192 : ℕ := 0xca9044dbd844
def s43 : List ℕ := [f189,f190,f191,f192]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w44 : Wide 24 4 s43 := viaSearch (by decide +kernel)
def p41 : Weak 150 24 := relaxed (pick [18,20,23,31,37,49,50,52,53,55,66,69,74,86,89,98,112,115,117,121,124,132,134,139] (by decide) (by decide) (by decide))
def r50 : Rule 150 8 := cutRule 8 p41 w44
def f193 : ℕ := 0x90cb8e
def f194 : ℕ := 0xbbd384
def f195 : ℕ := 0xd6e86a
def f196 : ℕ := 0xf52f12
def s44 : List ℕ := [f193,f194,f195,f196]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w45 : Wide 12 3 s44 := viaSearch (by decide +kernel)
def p42 : Weak 150 12 := signedPick 14 [14,18,44,67,74,91,101,103,112,121,124,132] (by decide) (by decide) (by decide)
def r51 : Rule 150 8 := cutRule 8 p42 w45
def f197 : ℕ := 0x40720595788f40f3
def f198 : ℕ := 0x420e40528c41c80a
def f199 : ℕ := 0xd13096209a3656d61
def f200 : ℕ := 0x108c0018221bf0b794
def f201 : ℕ := 0x2e2180a00dc43a1e0f
def s45 : List ℕ := [f197,f198,f199,f200,f201]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w46 : Wide 35 5 s45 := viaSearch (by decide +kernel)
def p43 : Weak 150 35 := relaxed (pick [1,9,10,13,20,29,32,40,42,49,50,51,52,54,56,64,65,66,69,71,78,79,82,86,89,98,106,113,114,115,117,135,139,141,146] (by decide) (by decide) (by decide))
def r52 : Rule 150 8 := cutRule 8 p43 w46
def f202 : ℕ := 0x382cf9383d
def f203 : ℕ := 0xb00c20fc7e6
def f204 : ℕ := 0x548511569559
def f205 : ℕ := 0xe0c301e0eb83
def s46 : List ℕ := [f202,f203,f204,f205]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w47 : Wide 24 4 s46 := viaSearch (by decide +kernel)
def p44 : Weak 150 24 := relaxed (pick [1,10,20,29,32,40,42,49,50,52,54,66,69,71,78,79,86,89,98,114,115,117,139,146] (by decide) (by decide) (by decide))
def r53 : Rule 150 8 := cutRule 8 p44 w47
def f206 : ℕ := 0xe7ce
def f207 : ℕ := 0x57e54c
def f208 : ℕ := 0x9e09e4
def f209 : ℕ := 0xacf2c6
def s47 : List ℕ := [f206,f207,f208,f209]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w48 : Wide 12 3 s47 := viaSearch (by decide +kernel)
def p45 : Weak 150 12 := signedPick 10 [10,40,70,71,78,83,95,105,107,114,146,148] (by decide) (by decide) (by decide)
def r54 : Rule 150 8 := cutRule 8 p45 w48
def f210 : ℕ := 0x922052d4
def f211 : ℕ := 0x1400928c16
def f212 : ℕ := 0x3701926032
def f213 : ℕ := 0x370197f132
def f214 : ℕ := 0x37bbf4d57e
def f215 : ℕ := 0x3fffffff94
def s48 : List ℕ := [f210,f211,f212,f213,f214,f215]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w49 : Wide 19 5 s48 := viaSearch (by decide +kernel)
def p46 : Weak 150 19 := signedPick 9 [9,10,11,13,42,49,51,56,64,65,68,81,82,86,89,92,113,114,141] (by decide) (by decide) (by decide)
def r55 : Rule 150 8 := cutRule 8 p46 w49
def f216 : ℕ := 0x429e5c254f3
def f217 : ℕ := 0xa40278760bbc
def f218 : ℕ := 0xa42bfdf65fff
def f219 : ℕ := 0x1192d009db7a0
def f220 : ℕ := 0x1f2840af95217
def f221 : ℕ := 0x242d0012bec4c
def s49 : List ℕ := [f216,f217,f218,f219,f220,f221]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w50 : Wide 25 5 s49 := viaSearch (by decide +kernel)
def p47 : Weak 150 25 := relaxed (pick [0,17,18,20,43,56,64,65,69,74,82,86,87,89,93,98,112,113,115,121,124,132,136,140,141] (by decide) (by decide) (by decide))
def r56 : Rule 150 8 := cutRule 8 p47 w50
def f222 : ℕ := 0x94dcffc07c7eda0c07c21aa844aa33a1303a425373ff01f1fb68b01f086aa11aa8ce86c0e9
def f223 : ℕ := 0xf3089fa6126d6f54a7af0399001f24a92210ebcc227e9849b5bd52bebd0e64007c92a488c3a
def s50 : List ℕ := [f121,f120,f123,f222,f223,f122,f118,f119]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem b0 : Ban 150 9 s50 := viaRules (ws := [s29]) (consBan b1 (nilBan _ _))
  (dictionary [(1025621453,r0),(130070418,r1),(1978492789,r2),(1781529055,r1),(1482467779,r0),(1407557199,r3),(1202894077,r3),(1810154720,r1),(439812773,r4),(2071515532,r1),(701173585,r5),(1167639022,r3),(1991912031,r0),(1475235689,r6),(218654500,r5),(55396110,r0),(901248965,r3),(1876383873,r1),(1287136336,r7),(278833124,r1),(1837069234,r4),(2095256065,r0),(1360194610,r0),(18777489,r8),(1170685289,r9),(581437752,r10),(632885023,r9),(43637486,r6),(2003406710,r0),(1124001374,r0),(170111033,r1),(1253323734,r4),(1581886717,r1),(517615771,r7),(1540318978,r3),(1084198620,r0),(109380292,r0),(616487976,r9),(1699700677,r6),(1475370678,r9),(411099732,r10),(1082988483,r11),(1815552331,r9),(143092093,r9),(632254924,r9),(1997045786,r9),(560606817,r3),(1697061652,r2),(674856812,r32),(1846074770,r3),(923600426,r0),(1673743723,r2),(503470124,r32),(480386462,r0),(621887496,r5),(2033652646,r33),(663310699,r34),(1589733243,r32),(2021401317,r35),(651059370,r5),(526293624,r8),(1364471477,r36),(775223940,r37),(1338503950,r0),(513856826,r38),(2072092936,r8),(1262115877,r0),(705107167,r39),(1788319868,r2),(499764356,r11),(549564959,r40),(1632777660,r0),(617269254,r3),(1913920309,r41),(1893208797,r42),(1362826260,r3),(2133941481,r0),(88370366,r43),(1757476246,r42),(1858880386,r0),(2051147507,r5),(183855018,r43),(1614672437,r42),(751445226,r5),(1944802223,r8),(1667719966,r0),(201792661,r42),(1645759171,r44),(482569422,r42),(1442170060,r32),(1573886314,r3),(1535489676,r45),(193916579,r46),(1216105628,r3),(1066221430,r0),(1605351302,r47),(1532489531,r46),(301590988,r0),(1513750812,r5),(1780869183,r48),(1663871777,r46),(1801726837,r5),(914380319,r49),(325132782,r8),(1561335674,r45),(298159614,r50),(1856395724,r0),(1116351987,r51),(1808927531,r52),(744656585,r0),(1634577572,r45),(408912013,r53),(1492124714,r11),(543188784,r54),(727229685,r32),(6204133,r55),(1722167304,r46),(1195956294,r32),(2142873440,r42),(769568955,r56),(1162410876,r46),(1010393777,r42)])
  (by decide) (by decide +kernel) (by decide +kernel)
theorem cert6 : Ban 150 9 bank := b0
end PEqualNP.Outside.L_meta_14582.B0
namespace PEqualNP.Outside.L_meta_14582
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def target (x : Fin 8 → Bool) := decide (∃ i < ([0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def witness : Circuit := ⟨[⟨.or,[5,6]⟩,⟨.or,[0,1]⟩,⟨.and,[8,9]⟩,⟨.or,[6,7]⟩,⟨.or,[2,5]⟩,⟨.and,[11,12]⟩,⟨.or,[0,3]⟩,⟨.or,[4,14]⟩,⟨.and,[7,15]⟩,⟨.or,[10,13]⟩,⟨.or,[16,17]⟩],18⟩
theorem shaped : Monotone2 witness := by simp [witness,Monotone2]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem cost : witness.size=11 := rfl
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem valid : ∀ x,witness.eval (List.ofFn x)=target x := by decide +kernel
def inputs : List ℕ := [0x3823982083f4280023e0020256035b1a0441c9e0ae70830fd0a4008f88488bf80f6c6813672,0x2863902c2386501256540a8131030c672564a8a98e49b09e19406959522b14c54cb39c9d92a,0x6a10ad95412e0a3464cc227806c3585c274721b842b65504ba38d1933489e01f0d61729d1cc,0x94dcffc07c7eda0c07c21aa844aa33a1303a425373ff01f1fb68b01f086aa11aa8ce86c0e9,0xf3089fa6126d6f54a7af0399001f24a92210ebcc227e9849b5bd52bebd0e64007c92a488c3a,0x42986480540900c9000021780850a0000212010a61b231713c4364cd009fe561738859494a0,0x402420800850088039004802c0080d00810c0d50b0eeca39c86207ee41a10b85223d4306,0x40000000800000218004c042120000088a802371ac4c82244231b728130708e84258622ad9]
def posBits : ℕ := 0x903557518f843698a08a436439c8834b9f68a4933d3d5a9c7c4a9b8c2a3ed04441254270e02a5b4f8b395581743f2eb84c5a59229d5c5459a8b04c3622948a60d88e35a2d0963331952f994a5c5e515442906c41c2a037783a262db4bcc2493249218323214d8586842ec83278705f9729253a458752298952869a2d5d262b92c460566888473e4e81279231c146ac8d3b919e445388
def negBits : ℕ := 0x103417110f803418200a03243848030b1f2824131d3c581c3c481b0c0a1e500401240230c0281b0f0b191501341f0e38481a19021d58145828300c1620148220580e1582c0161311150f190a1c1e505040802c40828017381a242c343cc0091248018203200d0582042cc03058501f17280538050712090950061a0d1d060b12c040164880073c0e80078230c0062c0d1b111e401308
def sample (bank : ℕ) (i : Fin 150) (j : Fin 8) := bank.testBit (8*i.val+j.val)

def seeds : List Wire := inputs.map (fun a => (false,a))
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem listed : ∀ i : Fin 150, seeds.map (read i.val)=List.ofFn (sample posBits i) ∧
    seeds.map (read (150+i.val))=List.ofFn (sample negBits i) := by decide +kernel
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem labels : ∀ i : Fin 150, target (sample posBits i)=true ∧ target (sample negBits i)=false := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem essential : ∀ a∈inputs, ∃ i : Fin 150, ∀ b∈inputs, b.testBit i.val≠b.testBit (150+i.val) → b=a := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem initial {k S} (live : Live 150 k S) (sub : ∀ a∈S,a∈inputs) : S=inputs.toFinset := by
  apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
  intro a ha
  obtain ⟨i,h⟩ := essential a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
  exact h b (sub b hb) sep ▸ hb
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem trace (C : Circuit) (fan : FanInTwo C) (eq : circuitFun 8 C=target) :
    ∃ k≤C.gates.countP counted, Live 150 k inputs.toFinset := by
  let final := execute C.gates seeds
  let out := final.getD C.output zero
  have ev (i : ℕ) : read i out = C.eval (seeds.map (read i)) := by
    rw [show read i out = (final.map (read i)).getD C.output false from (read_get i final C.output).symm]
    rw [show final=execute C.gates seeds from rfl,execute_read i _ _ fan];rfl
  have result (x : Fin 8 → Bool) : C.eval (List.ofFn x)=target x := congrFun eq x
  have good : Good 150 out.2 := by
    intro i hi same
    let j : Fin 150 := ⟨i,hi⟩
    have diff : read i out=read (150+i) out := by simp [read,same]
    have p := ev i;have n := ev (150+i)
    rw [(listed j).1,result,(labels j).1] at p
    rw [(listed j).2,result,(labels j).2] at n
    rw [p,n] at diff;contradiction
  have nz : out.2≠0 := by
    intro z;have bad := good 0 (by decide);simp [z] at bad
  have found : out.2∈ reps final := (get_simple final C.output).resolve_left nz
  obtain ⟨k,S,limit,live,sub⟩ := extract good nz C.gates seeds found
  have stays : ∀ a∈S, a∈inputs := by simpa [reps,seeds,List.map_map,Function.comp_def] using sub
  exact ⟨k,limit,initial live stays ▸ live⟩


set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem noCheap : Ban 150 9 inputs := B0.cert6
set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem eleven {k : ℕ} (run : Live 150 k inputs.toFinset) : 10≤k := by
  by_contra! small
  exact noCheap k (by omega) run
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
end PEqualNP.Outside.L_meta_14582
theorem PEqualNP.Outside.L_meta_14582 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fan _ ev
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gates,o⟩
  obtain ⟨D, shaped, cost, valid⟩ := PEqualNP.Outside.L_meta_14582.noSaving gates.length ⟨C,fan,le_rfl,ev⟩
  exact ⟨D.gates,D.output,shaped,cost,valid⟩
