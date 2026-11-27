import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_14776.Support

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

theorem smallByCut {m h f t : Nat} {v w : List Nat} (p : Projection m h) (bound : Wide h t w)
    (nd : v.Nodup := by decide) (mem : ∀ a∈v, p.toFun a=0 ∨ p.toFun a∈w := by decide +kernel)
    (cost : f≤t+(v.map p.toFun).count 0 := by decide +kernel) : Ban m f v :=
  viaCut p bound nd mem cost

theorem solid {m f : Nat} {v : List Nat} (bound : Ban m f v)
    (ess : ∀ a∈v, ∃ i : Fin m, ∀ b∈v, b.testBit i.val≠b.testBit (m+i.val) → b=a := by decide +kernel) :
    Wide m f v := widen ess bound

theorem bySubset {m f t : Nat} {v w : List Nat} (bound : Wide m t w)
    (sub : ∀ a∈v, a∈w := by decide +kernel) (le : f≤t := by decide) : Ban m f v := by
  intro j h hb
  exact bound ⟨j,v.toFinset,h.trans le,hb,fun x hx => sub x (List.mem_toFinset.mp hx)⟩

theorem checkedSmall {m f : Nat} {v : List Nat} (ex : search m f v = false := by decide +kernel)
    (nd : v.Nodup := by decide) : Ban m f v := viaSmall ex nd

def t0 := 0x4110414714090cc30f3cf
def t1 := 0x4054133117030370ccccfc
def t2 := 0x118e04143828c63830f0f0f
def t3 := 0x40d00ec02e8307c03f00ff0
def t4 := 0xbb2aa0000003ffffc000000
def t5 := 0xee000baa8003f8003fff000
def v0 := [t0,t1,t2,t3,t4,t5]
def t6 := 0x1000101100004000c0cc
def v1 := [t6,t0,t1,t2,t3,t4,t5]
def t7 := 0x110a00000000c6380000000
def v2 := [t0,t1,t7,t2,t3,t4,t5]
def t8 := 0xa88b80dccfc
def t9 := 0x82238a4333cf
def t10 := 0x1a01741f00ff0
def t11 := 0x2554001fff000
def t12 := 0x31c1c158e0f0f
def v3 := [t8,t9,t10,t11,t12]
def t13 := 0x200880100cc
def v4 := [t13,t8,t9,t10,t11,t12]
def t14 := 0x8aabba4fffff
def v5 := [t8,t9,t14,t10,t11,t12]
def t15 := 0x888300ccc30
def v6 := [t15,t8,t9,t10,t11,t12]
def t16 := 0x802302423303
def v7 := [t8,t16,t9,t10,t11,t12]
def t17 := 0xcf0
def v8 := [t17,t8,t9,t10,t11,t12]
def t18 := 0x1aa9ff9fdcffc
def v9 := [t8,t9,t10,t18,t11,t12]
def t19 := 0xa88b80dc00c
def v10 := [t19,t8,t9,t10,t11,t12]
def t20 := 0x1a01741f00300
def v11 := [t8,t9,t20,t10,t11,t12]
def t21 := 0x808100c0c0c
def v12 := [t21,t8,t9,t10,t11,t12]
def t22 := 0x31e9cbd8fcfff
def v13 := [t8,t9,t10,t11,t12,t22]
def t23 := 0x280a801c0f0
def v14 := [t23,t8,t9,t10,t11,t12]
def t24 := 0x3141405820303
def v15 := [t8,t9,t10,t11,t24,t12]
def t25 := 0xdc000
def v16 := [t25,t8,t9,t10,t11,t12]
def t26 := 0x25fc8b9fffcfc
def v17 := [t8,t9,t10,t11,t26,t12]
def t27 := 0xa88b8000cfc
def v18 := [t27,t8,t9,t10,t11,t12]
def t28 := 0x2554001f23000
def v19 := [t8,t9,t10,t28,t11,t12]
def t29 := 0x8003004003c0
def v20 := [t8,t29,t9,t10,t11,t12]
def t30 := 0x1a237cbf33fff
def v21 := [t8,t9,t10,t30,t11,t12]
def t31 := 0x2208a03300f
def v22 := [t31,t8,t9,t10,t11,t12]
def t32 := 0x1201441b00c30
def v23 := [t8,t9,t32,t10,t11,t12]
def t33 := 0x2030f
def v24 := [t33,t8,t9,t10,t11]
def v25 := [t33,t8,t9,t10,t11,t12]
def t34 := 0x39e3f9fcf3fcf
def v26 := [t8,t9,t10,t11,t12,t34]
def t35 := 0x82238a4130c0
def v27 := [t8,t35,t9,t10,t11]
def v28 := [t8,t35,t9,t10,t11,t12]
def t36 := 0x31c1c158c0c00
def v29 := [t8,t9,t10,t11,t36,t12]
def t37 := 0x433000
def v30 := [t37,t8,t9,t10,t11,t12]
def t38 := 0x2d7638bfff3cf
def v31 := [t8,t9,t10,t11,t38,t12]
def t39 := 0x82238a0003cf
def v32 := [t8,t39,t9,t10,t11,t12]
def t40 := 0x2554001bcc000
def v33 := [t8,t9,t10,t40,t11,t12]
def t41 := 0x1001401800f00
def v34 := [t8,t9,t41,t10,t11,t12]
def t42 := 0x3bc1f55fe0fff
def v35 := [t8,t9,t10,t11,t12,t42]
def t43 := 0xa003407000f0
def v36 := [t8,t9,t43,t10,t11,t12]
def t44 := 0x21c08140e000f
def v37 := [t8,t9,t10,t44,t11,t12]
def t45 := 0x1f00000
def v38 := [t45,t8,t9,t10,t11,t12]
def t46 := 0x3f55741fffff0
def v39 := [t8,t9,t10,t11,t12,t46]
def t47 := 0x1a01740000ff0
def v40 := [t8,t9,t47,t10,t11,t12]
def t48 := 0x25540000ff000
def v41 := [t8,t9,t10,t48,t11,t12]
def t49 := 0x21400018e0000
def v42 := [t8,t9,t10,t49,t11,t12]
def t50 := 0x35d5c15ffff0f
def v43 := [t8,t9,t10,t11,t50]
def v44 := [t8,t9,t10,t11,t12,t50]
def t51 := 0x1081c14000f0f
def v45 := [t8,t9,t51,t10,t11]
def v46 := [t8,t9,t51,t10,t11,t12]
def t52 := 0x41400071f000
def v47 := [t8,t52,t9,t10,t11,t12]
def p63_59 : Projection 46 25 := pick [12,13,14,15,4,5,6,7,20,21,22,23,26,27,28,29,30,39,40,41,34,35,36,44,45] rfl (by decide +kernel) (by decide)
def map63_4 : Projection 46 46 := pick [29,28,33,32,16,17,42,43,41,40,18,19,35,34,38,37,4,5,10,11,45,44,24,25,22,23,27,26,1,0,31,30,3,2,13,12,39,15,14,36,9,8,6,7,21,20] rfl (by decide +kernel) (by decide)
def t53 := 0x44551735774393fcfcffff
def v48 := [t0,t1,t53,t2,t3,t4,t5]
def v49 := [t6,t53,t2,t3,t4,t5]
def t54 := 0xbbaea414382bfffff0f0f0f
def v51 := [t6,t0,t53,t2,t3,t4,t5]
def v53 := [t6,t1,t53,t2,t3,t4,t5]
def t55 := 0x14f
def t56 := 0x4b3
def t57 := 0xa3c
def v55 := [t55,t56,t57]
def p63_42 : Projection 46 6 := pick [29,28,35,34,4,5] rfl (by decide +kernel) (by decide)
def v56 := [t6,t0,t1,t53,t2,t3,t4,t5]
def t58 := 0x40104046040908c303303
def v57 := [t58,t0,t53,t2,t3,t4,t5]
def v58 := [t58,t0,t1,t53,t2,t3,t4,t5]
def t59 := 0x4044132106030330cc0c30
def v59 := [t59,t1,t53,t2,t3,t4,t5]
def v60 := [t0,t59,t1,t53,t2,t3,t4,t5]
def v61 := [t0,t59,t1,t2,t3,t4,t5]
def t60 := 0x8404143828000030f0f0f
def v62 := [t0,t60,t1,t2,t3,t4,t5]
def t61 := 0x4000400600010003003c0
def v63 := [t61,t0,t1,t53,t2,t3,t4,t5]
def t62 := 0x40d11ec16f970fccff0ffff
def v64 := [t1,t53,t2,t3,t62,t4,t5]
def t63 := 0xff2aabaa8003ffffffff000
def t64 := 0x1331170ccccfc
def t65 := 0x1735774fcffff
def t66 := 0x414382b0f0f0f
def t67 := 0xbaa8003fff000
def t68 := 0xec02e83f00ff0
def t69 := 0xec16f97f0ffff
def v66 := [t64,t65,t66,t67,t68,t69]
def t70 := 0x41471430f3cf
def t71 := 0x537397bcfcfff
def t72 := 0xed43eabff0fff
def v67 := [t70,t64,t71,t67,t68,t72]
def v68 := [t70,t65,t71,t67,t68,t72]
def t73 := 0x1321060cc0c30
def v69 := [t70,t73,t71,t67,t68,t72]
def v70 := [t70,t64,t71,t67,t69,t72]
def t74 := 0xe802883c00c30
def v71 := [t70,t64,t71,t67,t74,t72]
def t75 := 0x404280b030303
def v72 := [t70,t64,t75,t67,t68,t72]
def v73 := [t70,t75,t71,t67,t68,t72]
def t76 := 0xc00cf0
def v74 := [t76,t70,t71,t67,t72]
def t77 := 0x414714f0ffff
def v75 := [t77,t71,t67,t72]
def v76 := [t76,t77,t71,t67,t72]
def v77 := [t70,t77,t71,t67,t72]
def t78 := 0xc00c30
def v78 := [t78,t70,t71,t67,t72]
def t79 := 0x41471430f30f
def v79 := [t76,t79,t71,t67,t72]
def t80 := 0x537397b0fc30f
def v80 := [t76,t70,t80,t67,t72]
def v81 := [t70,t80,t71,t67,t72]
def t81 := 0xed43eab3f030f
def v82 := [t76,t70,t71,t67,t81]
def v83 := [t70,t71,t67,t81,t72]
def t82 := 0xbaa8003fffcf0
def v84 := [t70,t71,t82,t72]
def v85 := [t76,t70,t71,t82,t72]
def v86 := [t70,t71,t67,t82,t72]
def v87 := [t17,t70,t71,t67,t72]
def t83 := 0xbaa80033ff000
def v88 := [t76,t70,t71,t83,t72]
def t84 := 0x414382bcf0fff
def v89 := [t76,t70,t84,t67]
def v90 := [t76,t70,t84,t71,t67]
def v91 := [t76,t70,t84,t67,t72]
def t85 := 0x123015000c000
def v92 := [t76,t70,t85,t71,t67]
def t86 := 0xac00680300000
def v93 := [t76,t70,t86,t67,t72]
def v94 := [t76,t70,t64,t71,t67,t72]
def v95 := [t76,t70,t71,t67,t68,t72]
def t87 := 0x13311700cc00c
def v96 := [t70,t87,t64,t71,t67,t72]
def t88 := 0xec02e83300300
def v97 := [t70,t71,t67,t88,t68,t72]
def t89 := 0x101020cc0cfc
def v98 := [t89,t70,t71,t67,t68]
def v99 := [t89,t70,t64,t71,t67,t68]
def v100 := [t89,t70,t71,t67,t68,t72]
def v101 := [t70,t85,t64,t71,t67,t68]
def t90 := 0xec42e8b330303
def v102 := [t70,t71,t67,t68,t90,t72]
def t91 := 0xbbb9173fffcfc
def v103 := [t70,t71,t67,t91,t68,t72]
def t92 := 0x111170000cfc
def v104 := [t92,t70,t71,t67,t68,t72]
def t93 := 0x4002803c00ff0
def v105 := [t70,t64,t93,t67,t72]
def v106 := [t70,t64,t93,t71,t67,t72]
def v107 := [t70,t64,t93,t67,t68,t72]
def t94 := 0x13711780fc00f
def v108 := [t70,t64,t94,t71,t67,t72]
def v109 := [t70,t64,t86,t67,t68,t72]
def v110 := [t70,t64,t84,t67,t68]
def v111 := [t70,t64,t84,t71,t67,t68]
def v112 := [t70,t64,t84,t67,t68,t72]
def t95 := 0x1410280f000f
def v113 := [t95,t70,t64,t71,t67,t68]
def v114 := [t95,t70,t64,t71,t67,t72]
def t96 := 0xfeaae83fffff0
def v115 := [t70,t64,t71,t67,t72,t96]
def t97 := 0x4402e80000ff0
def v116 := [t70,t64,t97,t71,t67,t72]
def map31_4 : Projection 26 26 := pick [1,0,3,2,4,5,10,11,9,8,6,7,16,17,18,19,12,13,14,15,24,25,22,23,20,21] rfl (by decide +kernel) (by decide)
def p63_62 : Projection 46 26 := pick [29,28,33,32,16,17,42,43,41,40,18,19,35,34,38,37,4,5,10,11,45,44,24,25,22,23] rfl (by decide +kernel) (by decide)
def v117 := [t0,t1,t53,t2,t3,t62,t4,t5]
def t98 := 0x110014114080cc00f00f
def v118 := [t98,t1,t53,t2,t3,t4,t5]
def v119 := [t98,t0,t1,t53,t2,t3,t4,t5]
def t99 := 0x40900e80288306c03c00c30
def v120 := [t0,t1,t53,t2,t99,t3,t4,t5]
def t100 := 0x8000030f
def v121 := [t100,t0,t1,t53,t2,t3,t4,t5]
def t101 := 0x11cf14557f3ccf3cf3fffcf
def v122 := [t0,t1,t53,t2,t101,t3,t4,t5]
def t102 := 0x41104147140904c30f0c0
def v123 := [t102,t0,t1,t53,t2,t3,t4,t5]
def t103 := 0x118e04143828c63030f0c00
def v124 := [t0,t1,t53,t103,t2,t3,t4,t5]
def t104 := 0x800030f000
def v125 := [t104,t0,t1,t53,t2,t3,t4,t5]
def t105 := 0xee411bebc717f90cffff3cf
def v126 := [t0,t1,t53,t2,t3,t4,t5,t105]
def t106 := 0x4110414714010cc0003cf
def v127 := [t106,t0,t1,t53,t2,t3,t4,t5]
def t107 := 0xee000baa8003f0003cf0000
def v128 := [t0,t1,t53,t2,t3,t4,t107,t5]
def t108 := 0x90cc000000
def v129 := [t108,t0,t1,t53,t2,t3,t4,t5]
def t109 := 0xbb6bb0414717ffffc30f3cf
def v130 := [t1,t53,t2,t3,t4,t109,t5]
def v131 := [t0,t1,t2,t3,t109,t54,t5]
def v132 := [t8,t14,t10,t11,t38,t12]
def v133 := [t8,t16,t10,t11,t38,t12]
def t110 := 0x200880dc0cc
def v134 := [t110,t8,t9,t10,t11,t12]
def t111 := 0x2dfebbbffffff
def v135 := [t8,t9,t10,t11,t111,t12]
def t112 := 0x88830000c30
def v136 := [t112,t8,t9,t10,t11,t12]
def t113 := 0x2d56303f23303
def v137 := [t8,t9,t10,t11,t113,t12]
def v138 := [t8,t10,t30,t11,t38,t12]
def v139 := [t31,t8,t10,t11,t38,t12]
def v140 := [t33,t8,t9,t10,t11,t38]
def v141 := [t8,t35,t9,t10,t11,t38]
def v142 := [t37,t8,t10,t38,t12]
def v143 := [t37,t8,t9,t10,t38,t12]
def v144 := [t37,t8,t10,t11,t38,t12]
def v145 := [t8,t39,t9,t10,t38,t12]
def v146 := [t8,t10,t40,t11,t38,t12]
def t114 := 0x800301f003c0
def v147 := [t8,t114,t9,t10,t11,t12]
def t115 := 0x3f777cbffffff
def v148 := [t8,t9,t10,t11,t12,t115]
def t116 := 0x1201440000c30
def v149 := [t8,t9,t116,t10,t11,t12]
def t117 := 0x257608a0ff00f
def v150 := [t8,t9,t10,t11,t117,t12]
def v151 := [t8,t9,t10,t38,t50]
def v152 := [t8,t9,t10,t38,t12,t50]
def v153 := [t8,t9,t10,t11,t38,t50]
def v154 := [t8,t9,t51,t10,t11,t38]
def v155 := [t8,t52,t9,t10,t38,t12]
def t118 := 0x21400018e030f
def v156 := [t8,t9,t10,t118,t11]
def v157 := [t8,t9,t10,t118,t11,t12]
def v158 := [t8,t9,t10,t118,t11,t38]
def t119 := 0x3df7f9fffffcf
def v159 := [t8,t9,t10,t11,t12,t119]
def t120 := 0x1081c14000c00
def v160 := [t8,t9,t120,t10,t11,t12]
def t121 := 0xc3638a71f0c0
def v161 := [t8,t9,t121,t10,t11]
def v162 := [t8,t9,t121,t10,t11,t12]
def v163 := [t8,t9,t121,t10,t11,t38]
def v164 := [t0,t1,t53,t2,t3,t4,t109,t5]
def t122 := 0x41104147140000030f3cf
def v165 := [t122,t1,t53,t2,t3,t4,t5]
def t123 := 0xcc000
def v166 := [t123,t8,t9,t10,t11,t12]
def t124 := 0x25fc8b9bdccfc
def v167 := [t8,t9,t10,t11,t124,t12]
def t125 := 0xa88b8010cfc
def v168 := [t125,t8,t9,t10,t11,t12]
def t126 := 0x2554001b00000
def v169 := [t8,t9,t10,t126,t11,t12]
def v170 := [t33,t8,t10,t40,t11]
def v171 := [t33,t8,t9,t10,t40,t11]
def v172 := [t33,t8,t10,t40,t11,t12]
def v173 := [t8,t35,t9,t10,t40,t11]
def v174 := [t8,t10,t40,t11,t36,t12]
def v175 := [t37,t8,t9,t10,t40,t12]
def v176 := [t8,t39,t10,t40,t12]
def v177 := [t8,t39,t9,t10,t40,t12]
def v178 := [t8,t39,t10,t40,t11,t12]
def t127 := 0x1b00000
def v179 := [t127,t8,t9,t10,t11,t12]
def t128 := 0x3f55741fccff0
def v180 := [t8,t9,t10,t11,t12,t128]
def t129 := 0x1a01740400ff0
def v181 := [t8,t9,t129,t10,t11,t12]
def t130 := 0x25540000cc000
def v182 := [t8,t9,t10,t130,t11,t12]
def t131 := 0x21400018c0000
def v183 := [t8,t9,t10,t131,t11,t12]
def t132 := 0x35d5c15becf0f
def v184 := [t8,t9,t10,t11,t132]
def v185 := [t8,t9,t10,t11,t12,t132]
def v186 := [t8,t9,t10,t40,t11,t132]
def t133 := 0x1081c14020f0f
def v187 := [t8,t9,t133,t10,t11]
def v188 := [t8,t9,t133,t10,t11,t12]
def v189 := [t8,t9,t133,t10,t40,t11]
def t134 := 0x41400030c000
def v190 := [t8,t134,t9,t10,t11,t12]
def v191 := [t8,t9,t10,t40,t50]
def v192 := [t8,t9,t10,t40,t12,t50]
def v193 := [t8,t9,t10,t40,t11,t50]
def v194 := [t8,t9,t51,t10,t40,t11]
def v195 := [t8,t52,t9,t10,t40,t12]
def p63_61 : Projection 46 25 := pick [35,34,38,37,16,17,42,43,45,44,24,25,27,26,1,0,31,36,9,8,13,12,39,21,20] rfl (by decide +kernel) (by decide)
def v196 := [t122,t0,t1,t53,t2,t3,t4,t5]
def t135 := 0xbb2aa0000003f6f30000000
def v197 := [t0,t1,t53,t2,t3,t135,t4,t5]
def v198 := [t58,t0,t1,t2,t3,t4,t5]
def v199 := [t76,t0,t53,t2,t3,t4,t5]
def p63_55 : Projection 46 25 := pick [29,28,33,32,16,17,42,43,41,40,18,19,27,26,1,0,31,30,3,2,13,12,39,15,14] rfl (by decide +kernel) (by decide)
def map63_2 : Projection 46 46 := pick [0,1,8,9,5,4,7,6,2,3,11,10,12,13,20,21,16,17,24,25,14,15,23,22,18,19,26,27,34,35,36,31,37,38,28,29,30,32,33,39,44,45,42,43,40,41] rfl (by decide +kernel) (by decide)
def v201 := [t76,t0,t1,t53,t2,t3,t4,t5]
def p63_21 : Projection 46 6 := pick [0,1,12,13,16,17] rfl (by decide +kernel) (by decide)
def t136 := 0x44d54ff33ff337f73fccffc
def v202 := [t0,t1,t53,t2,t3,t136,t4,t5]
def t137 := 0x40541331170303700cc00c
def v203 := [t0,t137,t1,t53,t2,t3,t4,t5]
def t138 := 0x40d00ec02e8307c03300300
def v204 := [t0,t53,t2,t138,t3,t4,t5]
def v206 := [t0,t1,t53,t2,t138,t3,t4,t5]
def t139 := 0x400101020003000c0c0c
def v207 := [t139,t0,t1,t53,t2,t3,t4,t5]
def t140 := 0x158f45373978f63f3cfcfff
def v208 := [t0,t53,t2,t140,t3,t4,t5]
def t141 := 0xee054bbb9173f8373fffcfc
def v209 := [t0,t1,t2,t3,t4,t141,t63]
def v210 := [t70,t64,t66,t67,t69,t72]
def v211 := [t64,t65,t66,t67,t69,t72]
def t142 := 0x404604303303
def v212 := [t142,t64,t66,t67,t69,t72]
def v213 := [t70,t64,t66,t67,t74,t72]
def v214 := [t64,t66,t67,t74,t69,t72]
def t143 := 0x4006003003cf
def v215 := [t143,t64,t66,t67,t69]
def v216 := [t143,t70,t64,t66,t67,t69]
def v217 := [t143,t64,t66,t67,t69,t72]
def t144 := 0x1411400f000
def v218 := [t144,t70,t64,t66,t67,t69]
def t145 := 0xe9438abcf0c30
def v219 := [t64,t66,t67,t145,t69,t72]
def v220 := [t70,t64,t75,t67,t69,t72]
def t146 := 0x4002803000f0f
def v221 := [t70,t64,t146,t67,t72]
def v222 := [t70,t64,t146,t66,t67,t72]
def v223 := [t70,t64,t146,t67,t69,t72]
def t147 := 0x1410280f0000
def v224 := [t147,t70,t64,t66,t67,t72]
def t148 := 0xac14794f0f0f0
def v225 := [t70,t64,t148,t67,t69,t72]
def t149 := 0xac00680f000f0
def v226 := [t70,t64,t66,t149,t67,t69]
def v227 := [t70,t64,t149,t67,t69,t72]
def t150 := 0x10110c0ccfc
def v228 := [t150,t70,t66,t67,t72]
def v229 := [t150,t70,t64,t66,t67,t72]
def v230 := [t150,t70,t66,t67,t69,t72]
def t151 := 0x13210600c0000
def v231 := [t70,t151,t64,t66,t67,t72]
def t152 := 0xec06e87303303
def v232 := [t70,t66,t67,t152,t69,t72]
def v233 := [t89,t70,t66,t67,t69]
def v234 := [t89,t70,t64,t66,t67,t69]
def v235 := [t89,t70,t66,t67,t69,t72]
def v236 := [t70,t85,t64,t66,t67,t69]
def v237 := [t70,t66,t67,t69,t90,t72]
def t153 := 0xec02e83f00fff
def v238 := [t70,t64,t66,t67,t153]
def v239 := [t70,t64,t66,t67,t153,t69]
def v240 := [t70,t64,t66,t67,t153,t72]
def t154 := 0xfebef97ffffff
def v241 := [t70,t64,t66,t67,t72,t154]
def t155 := 0x4416f94000fff
def v242 := [t70,t64,t66,t155,t67,t72]
def t156 := 0xffebeabffffff
def v243 := [t70,t64,t66,t67,t69,t156]
def t157 := 0x4543ea8000fff
def v244 := [t70,t64,t66,t157,t67,t69]
def map63_5 : Projection 46 46 := pick [35,34,38,37,16,17,42,43,45,44,24,25,29,28,33,32,5,4,11,10,41,40,18,19,23,22,27,26,1,0,31,36,9,8,13,12,39,21,20,30,3,2,7,6,15,14] rfl (by decide +kernel) (by decide)
def map63_6 : Projection 46 46 := pick [29,28,41,40,17,16,43,42,33,32,19,18,35,34,45,44,4,5,22,23,38,37,25,24,10,11,27,26,13,12,39,30,15,14,1,0,31,3,2,36,21,20,6,7,9,8] rfl (by decide +kernel) (by decide)
def v245 := [t0,t1,t53,t2,t140,t3,t4,t5]
def t158 := 0x4014123015030070c0c0f0
def v246 := [t0,t158,t53,t2,t3,t4,t5]
def v247 := [t0,t158,t1,t53,t2,t3,t4,t5]
def t159 := 0x118a04042808c6083030303
def v248 := [t0,t1,t53,t159,t2,t3,t4,t5]
def t160 := 0x4000122000030000ccc000
def v249 := [t0,t160,t1,t53,t2,t3,t4,t5]
def v250 := [t0,t53,t2,t3,t4,t5,t141]
def map63_7 : Projection 46 46 := pick [35,34,45,44,17,16,43,42,38,37,25,24,29,28,41,40,5,4,23,22,33,32,19,18,11,10,27,26,13,12,39,36,21,20,1,0,31,9,8,30,15,14,7,6,3,2] rfl (by decide +kernel) (by decide)
def v251 := [t0,t1,t53,t2,t3,t4,t5,t141]
def t161 := 0x54011117000370000cfc
def v252 := [t161,t0,t53,t2,t3,t4,t5]
def v253 := [t161,t0,t1,t53,t2,t3,t4,t5]
def t162 := 0xea000a888003c8003333000
def v254 := [t0,t1,t53,t2,t3,t4,t162,t5]
def t163 := 0x30370000000
def v255 := [t163,t0,t1,t53,t2,t3,t4,t5]
def t164 := 0xbf2fe1331173ffffcccccfc
def v256 := [t0,t53,t2,t3,t4,t164,t5]
def v257 := [t0,t1,t2,t3,t4,t105,t63]
def v258 := [t1,t2,t101,t3,t4,t105,t63]
def v259 := [t102,t1,t2,t3,t4,t105,t63]
def v260 := [t0,t1,t2,t3,t4,t107,t63]
def v261 := [t1,t2,t3,t4,t107,t105,t63]
def v262 := [t0,t1,t2,t3,t109,t105,t63]
def v263 := [t0,t1,t2,t3,t135,t105,t63]
def t165 := 0x90cc30f000
def v264 := [t165,t1,t2,t3,t4,t105]
def map63_1 : Projection 46 46 := pick [12,13,14,15,4,5,6,7,20,21,22,23,0,1,2,3,17,16,19,18,8,9,10,11,25,24,26,27,28,29,30,39,40,41,34,35,36,44,45,31,32,33,43,42,37,38] rfl (by decide +kernel) (by decide)
def v266 := [t165,t0,t1,t2,t3,t4,t105]
def v267 := [t165,t1,t2,t3,t4,t105,t63]
def t167 := 0x4110414714000000003cf
def v268 := [t167,t0,t1,t2,t3,t4,t105]
def t168 := 0xff2aabaa8003f6f33cf0000
def v269 := [t1,t2,t3,t4,t105,t168,t63]
def t169 := 0xee455bfbd777f93ffffffff
def v270 := [t0,t1,t2,t3,t4,t169,t63]
def t170 := 0xea401ac8c607c908f333303
def v271 := [t0,t1,t2,t3,t4,t170,t63]
def t171 := 0xeed11febef97ffccfffffff
def v272 := [t0,t1,t2,t3,t4,t171,t63]
def t172 := 0xae01112bc114f80cc0ff00f
def v273 := [t0,t1,t2,t3,t172,t4,t63]
def t173 := 0xc00830f030f
def v274 := [t173,t0,t1,t3,t4,t63]
def v276 := [t173,t0,t1,t2,t3,t4,t63]
def v277 := [t173,t0,t1,t3,t4,t105,t63]
def t175 := 0x118e0414382806300000c00
def v278 := [t0,t1,t175,t2,t3,t4,t63]
def t176 := 0xee411bebc7173904cf0f0c0
def v279 := [t0,t1,t3,t4,t176,t105,t63]
def v280 := [t0,t1,t2,t3,t54,t105,t63]
def t177 := 0xaa20a000000339c7c000000
def v281 := [t0,t1,t2,t3,t177,t105,t63]
def t178 := 0xffaeafbeb82bfffffffff0f
def v282 := [t0,t1,t2,t3,t4,t105,t178]
def t179 := 0xee20abaa800339c7cf0f000
def v283 := [t0,t1,t2,t3,t4,t179,t105]
def t180 := 0xaa0000000003f90cc000000
def v284 := [t0,t1,t2,t3,t180,t63]
def v285 := [t0,t1,t2,t3,t180,t105,t63]
def v286 := [t0,t1,t2,t3,t180,t4,t63]
def t181 := 0x44411bebc71400003fff3cf
def v287 := [t0,t1,t2,t3,t181,t105,t63]
def t182 := 0x112aa000000006f30000000
def v288 := [t0,t1,t182,t2,t3,t4,t63]
def t183 := 0xee000baa8003f90cffff000
def v289 := [t0,t1,t2,t3,t4,t183]
def v290 := [t0,t1,t2,t3,t4,t183,t105]
def v291 := [t0,t1,t2,t3,t4,t183,t63]
def t184 := 0x44000baa800000003fff000
def v292 := [t0,t1,t2,t3,t184,t4,t105]
def v293 := [t0,t1,t2,t3,t184,t105,t63]
def v294 := [t0,t1,t53,t2,t3,t4,t164,t5]
def t185 := 0x4054133117000000ccccfc
def v295 := [t0,t185,t53,t2,t3,t4,t5]
def v296 := [t0,t185,t1,t53,t2,t3,t4,t5]
def t186 := 0xbb2aa0000003cfc8c000000
def v297 := [t0,t1,t53,t2,t3,t186,t4,t5]
def t187 := 0x400040060001000f00ff0
def v298 := [t187,t0,t1,t2,t3,t4,t5]
def v300 := [t187,t0,t1,t53,t2,t3,t4,t5]
def t189 := 0x44d55ff37ff73fffffcffff
def v301 := [t0,t1,t2,t3,t189,t4,t5]
def v302 := [t0,t1,t2,t3,t4,t5,t178]
def v303 := [t0,t1,t101,t3,t4,t5,t178]
def v304 := [t0,t1,t103,t3,t4,t5,t178]
def v305 := [t0,t1,t2,t3,t4,t107,t178]
def v306 := [t0,t1,t2,t3,t109,t5,t178]
def v307 := [t0,t1,t2,t3,t135,t5,t178]
def t190 := 0x90cc30f30f
def v308 := [t190,t1,t2,t3,t4,t5]
def v309 := [t190,t0,t1,t2,t3,t4,t5]
def v310 := [t190,t1,t2,t3,t4,t5,t178]
def t191 := 0xffefbfffff3ffffffffffcf
def v311 := [t0,t1,t2,t3,t4,t5,t191]
def t192 := 0x4110414714000000000c0
def v312 := [t192,t0,t1,t2,t3,t4,t5]
def t193 := 0xffaeafbeb82bf6f33cf0c00
def v313 := [t1,t2,t3,t4,t5,t193]
def v314 := [t0,t1,t2,t3,t4,t5,t193]
def v315 := [t1,t2,t3,t4,t5,t193,t178]
def t194 := 0x4040132102030370cccc0c
def v316 := [t0,t194,t1,t2,t3,t4,t5]
def t195 := 0xffafefbfb97bfffffffffff
def v317 := [t0,t1,t2,t3,t4,t5,t195]
def t196 := 0x140010150000000000f0
def v318 := [t196,t0,t1,t2,t3,t4,t5]
def t197 := 0xfbaaae8ca80bcfc8f333303
def v319 := [t0,t1,t2,t3,t4,t5,t197]
def t198 := 0x40800e80280307c03f00f00
def v320 := [t0,t1,t2,t198,t3,t4,t5]
def t199 := 0xfffeaffebeabfffffffffff
def v321 := [t0,t1,t2,t3,t4,t5,t199]
def t200 := 0x5000400680000000000f0
def v322 := [t0,t200,t1,t2,t3,t4,t5]
def t201 := 0xbf2ea13e9028f83fc0ff00f
def v323 := [t0,t1,t2,t3,t4,t201,t5]
def t202 := 0xc00030f0000
def v324 := [t202,t0,t1,t3,t4,t178]
def v326 := [t202,t0,t1,t2,t3,t4,t178]
def v327 := [t202,t0,t1,t3,t4,t5,t178]
def t203 := 0x118e0414382806380000f0f
def v328 := [t0,t1,t203,t2,t3,t4,t178]
def t204 := 0xee000baa800338000f0f000
def v329 := [t0,t1,t3,t4,t204,t5,t178]
def v330 := [t0,t1,t2,t3,t4,t5,t179]
def v331 := [t0,t1,t3,t4,t5,t179,t178]
def t205 := 0x11aea414382807ffc000f0f
def v332 := [t0,t1,t2,t205,t3,t4,t5]
def v333 := [t0,t1,t2,t205,t3,t4,t178]
def t206 := 0x44840fbeb82800003ffff0f
def v334 := [t0,t1,t2,t3,t206,t4,t5]
def v335 := [t0,t1,t2,t3,t206,t5,t178]
def v336 := [t0,t1,t53,t2,t3,t189,t4,t5]
def t207 := 0x40551335174383fc0cf00f
def v337 := [t0,t1,t207,t2,t3,t4,t5]
def t208 := 0x1c000
def v338 := [t208,t8,t9,t10,t11,t12]
def t209 := 0x4bc8b87dfcfc
def v339 := [t8,t209,t9,t10,t11,t12]
def t210 := 0xa88b80c0cfc
def v340 := [t210,t8,t9,t10,t11,t12]
def t211 := 0x414000703000
def v341 := [t8,t211,t9,t10,t11,t12]
def t212 := 0x413000
def v342 := [t212,t8,t9,t10,t11,t12]
def t213 := 0xc3638a73f3cf
def v343 := [t8,t9,t213,t10,t11,t12]
def t214 := 0x82238a0203cf
def v344 := [t8,t214,t9,t10,t11,t12]
def v345 := [t33,t8,t52,t9,t10,t11]
def v346 := [t8,t52,t35,t9,t10,t11]
def t215 := 0x700000
def v347 := [t215,t8,t9,t10,t11,t12]
def t216 := 0x1e15741f1fff0
def v348 := [t8,t9,t10,t216,t11,t12]
def t217 := 0x1a01741800ff0
def v349 := [t8,t9,t217,t10,t11,t12]
def t218 := 0x41400001f000
def v350 := [t8,t218,t9,t10,t11,t12]
def v351 := [t8,t52,t9,t10,t11,t50]
def v352 := [t8,t52,t9,t10,t49,t12]
def v353 := [t8,t52,t9,t51,t10]
def v354 := [t8,t52,t9,t51,t10,t12]
def v355 := [t8,t52,t9,t51,t10,t11]
def v356 := [t0,t1,t207,t53,t2,t3,t4,t5]
def t219 := 0x40900e80288306c03000000
def v357 := [t0,t1,t2,t219,t3,t4,t5]
def v358 := [t0,t1,t53,t2,t219,t3,t4,t5]
def t220 := 0x400101020003800c0f0f
def v359 := [t220,t0,t1,t2,t3,t4,t5]
def v361 := [t220,t0,t1,t53,t2,t3,t4,t5]
def t222 := 0x15cf55777f7cff3ffffffff
def v362 := [t0,t1,t2,t222,t3,t4,t5]
def v363 := [t0,t1,t53,t2,t222,t3,t4,t5]
def t223 := 0x441516347543907cf0f0f0
def v364 := [t0,t1,t223,t2,t3,t4,t5]
def t224 := 0x4550515774013fc000fff
def v365 := [t0,t224,t1,t2,t3,t4,t5]
def t225 := 0x25d48140ff00f
def v366 := [t8,t9,t10,t11,t225,t12]
def v367 := [t17,t8,t9,t11,t225,t12]
def v368 := [t19,t8,t9,t11,t225,t12]
def v369 := [t8,t9,t10,t11,t225,t22]
def v370 := [t8,t9,t10,t11,t225,t24]
def t226 := 0x808100dc00c
def v371 := [t226,t8,t9,t10,t11,t12]
def t227 := 0x25fc8bc0ffcff
def v372 := [t8,t9,t10,t11,t227,t12]
def t228 := 0x280a8000cf0
def v373 := [t228,t8,t9,t10,t11,t12]
def t229 := 0x2554004023003
def v374 := [t8,t9,t10,t11,t229,t12]
def v375 := [t33,t8,t9,t10,t11,t225]
def v376 := [t8,t35,t9,t10,t11,t225]
def t230 := 0x3300f
def v377 := [t230,t8,t9,t10,t11,t12]
def t231 := 0x2df6b9e4ff3cf
def v378 := [t8,t9,t10,t11,t231,t12]
def t232 := 0x82238a4003c0
def v379 := [t8,t232,t9,t10,t11,t12]
def t233 := 0x25d48140cc000
def v380 := [t8,t9,t10,t11,t233,t12]
def v381 := [t8,t9,t41,t10,t11,t225]
def v382 := [t8,t9,t11,t225,t12,t42]
def v383 := [t8,t9,t43,t11,t225]
def v384 := [t8,t9,t43,t10,t11,t225]
def v385 := [t8,t9,t43,t11,t225,t12]
def v386 := [t8,t9,t11,t225,t12,t46]
def v387 := [t8,t9,t47,t11,t225,t12]
def t234 := 0x3fd5f55ffffff
def v388 := [t8,t9,t10,t11,t12,t234]
def v389 := [t8,t9,t11,t225,t12,t234]
def v390 := [t8,t9,t10,t11,t225,t50]
def v391 := [t8,t9,t51,t10,t11,t225]
def t235 := 0x35d5c158fff0f
def v392 := [t8,t9,t10,t11,t235]
def v393 := [t8,t9,t10,t11,t12,t235]
def v394 := [t8,t9,t10,t11,t225,t235]
def t236 := 0x25d4815fff00f
def v395 := [t8,t9,t10,t11,t236,t12]
def t237 := 0x8081400000f
def v396 := [t237,t8,t9,t10,t11,t12]
def v397 := [t0,t1,t223,t53,t2,t3,t4,t5]
def t238 := 0x118a04042808c6003030000
def v398 := [t0,t1,t238,t2,t3,t4,t5]
def v399 := [t0,t1,t53,t238,t2,t3,t4,t5]
def t239 := 0x4000122000038000fcf000
def v400 := [t0,t239,t1,t2,t3,t4,t5]
def map63_3 : Projection 46 46 := pick [12,13,20,21,5,4,7,6,14,15,23,22,0,1,8,9,17,16,25,24,2,3,11,10,19,18,26,27,34,35,36,39,44,45,28,29,30,40,41,31,37,38,43,42,32,33] rfl (by decide +kernel) (by decide)
def v401 := [t0,t239,t1,t53,t2,t3,t4,t5]
def v402 := [t0,t1,t2,t3,t4,t5,t169]
def v403 := [t0,t1,t53,t2,t3,t4,t5,t169]
def v404 := [t0,t224,t1,t53,t2,t3,t4,t5]
def t240 := 0xea000a888003c0003030000
def v405 := [t0,t1,t2,t3,t4,t240,t5]
def v406 := [t0,t1,t53,t2,t3,t4,t240,t5]
def t241 := 0x393fc000000
def v407 := [t241,t0,t1,t2,t3,t4,t5]
def v409 := [t241,t0,t1,t53,t2,t3,t4,t5]
def t242 := 0xbf6ff1735777ffffcfcffff
def v411 := [t0,t1,t2,t3,t4,t242,t5]
def v412 := [t0,t1,t53,t2,t3,t4,t242,t5]
def t243 := 0x4455173577400000fcffff
def v413 := [t0,t1,t243,t2,t3,t4,t5]
def v414 := [t0,t1,t243,t53,t2,t3,t4,t5]
def t244 := 0xbb2aa0000003c6c00000000
def v415 := [t0,t1,t2,t3,t244,t4,t5]
def v416 := [t167,t0,t1,t2,t3,t4,t5]
def v417 := [t0,t1,t53,t2,t3,t244,t4,t5]
def t245 := 0x800400280006003000f00
def v418 := [t0,t245,t1,t53,t2,t3,t4,t5]
def t246 := 0x51de0ed43eabc7f83ff0fff
def v419 := [t0,t1,t53,t2,t3,t246,t4,t5]
def t247 := 0x40500ac0068301c00f000f0
def v420 := [t0,t1,t53,t2,t247,t3,t4,t5]
def t248 := 0x110e00141028c03800f000f
def v421 := [t0,t1,t53,t248,t2,t3,t4,t5]
def t249 := 0x40000a80000300003f00000
def v422 := [t0,t1,t53,t2,t249,t3,t4,t5]
def t250 := 0xeed00feaae83ffc03fffff0
def v423 := [t0,t1,t53,t2,t3,t4,t5,t250]
def t251 := 0xd004402e8007c00000ff0
def v424 := [t0,t251,t1,t53,t2,t3,t4,t5]
def t252 := 0xae00012a8000f80000ff000
def v425 := [t0,t1,t53,t2,t3,t252,t4,t5]
def t253 := 0x307c00000000
def v426 := [t253,t0,t1,t53,t2,t3,t4,t5]
def t254 := 0xfbfaaec02e83ffffff00ff0
def v428 := [t0,t1,t53,t2,t3,t4,t5,t254]
def t255 := 0x40d00ec02e8000003f00ff0
def v429 := [t0,t1,t53,t2,t255,t3,t4,t5]
def t256 := 0xbb2aa0000000f83fc000000
def v431 := [t0,t1,t53,t2,t3,t256,t4,t5]
def v432 := [t106,t0,t1,t2,t3,t4,t54,t5]
def v433 := [t202,t0,t1,t53,t2,t3,t4,t5]
def t257 := 0xff8e0fbeb82bfe383ffff0f
def v435 := [t0,t1,t53,t2,t3,t4,t5,t257]
def v436 := [t0,t1,t53,t203,t2,t3,t4,t5]
def v437 := [t0,t1,t53,t2,t3,t4,t204,t5]
def v438 := [t0,t1,t53,t7,t2,t3,t4,t5]
def v439 := [t0,t1,t53,t2,t3,t4,t54,t5]
def v440 := [t0,t60,t1,t53,t2,t3,t4,t5]
def v441 := [t0,t1,t53,t2,t3,t177,t4,t5]
def t258 := 0xaa0000000003f8000000000
def v442 := [t0,t1,t53,t2,t3,t258,t4,t5]
def v443 := [t0,t1,t53,t2,t3,t4,t5,t63]
def v444 := [t0,t1,t53,t2,t3,t184,t4,t5]
def t259 := 0x112aa000000007ffc000000
def v445 := [t0,t1,t53,t259,t2,t3,t4,t5]
def v446 := [t6,t58,t1,t2,t3,t4,t5]
def v447 := [t6,t58,t0,t1,t2,t3,t4,t5]
def t260 := 0x400040060001000300300
def v448 := [t260,t0,t1,t2,t3,t4,t5]
def v449 := [t260,t58,t0,t1,t2,t3,t4,t5]
def t261 := 0x40d01ec06e870fc8ff03ff3
def v450 := [t0,t1,t2,t261,t4,t5]
def t262 := 0xee20abaa8003f9c7ffff000
def v451 := [t0,t1,t2,t3,t4,t262]
def v452 := [t6,t0,t1,t2,t3,t4,t262]
def v453 := [t0,t1,t53,t2,t3,t4,t262]
def v454 := [t58,t0,t1,t2,t3,t4,t262]
def v455 := [t0,t59,t1,t2,t3,t4,t262]
def v456 := [t61,t0,t1,t2,t3,t4,t262]
def v457 := [t0,t1,t2,t3,t62,t4,t262]
def v458 := [t98,t0,t1,t2,t3,t4,t262]
def v459 := [t0,t1,t2,t99,t3,t4,t262]
def v460 := [t100,t0,t1,t2,t3,t4,t262]
def v461 := [t0,t1,t2,t101,t3,t4,t262]
def v462 := [t102,t0,t1,t2,t3,t4,t262]
def v463 := [t0,t1,t103,t2,t3,t4,t262]
def t263 := 0x904c30f000
def v464 := [t263,t0,t1,t2,t3,t4,t262]
def t264 := 0xee61bbebc717f9cfffff3cf
def v465 := [t0,t1,t2,t3,t4,t262,t264]
def t265 := 0x4110414714000800003cf
def v466 := [t265,t0,t1,t2,t3,t4,t262]
def t266 := 0xee20abaa8003f0c33cf0000
def v467 := [t0,t1,t2,t3,t4,t266,t262]
def v468 := [t108,t0,t1,t2,t3,t4,t262]
def v469 := [t0,t1,t2,t3,t109,t262]
def v470 := [t0,t1,t2,t3,t4,t109,t262]
def v471 := [t122,t0,t1,t2,t3,t4,t262]
def v472 := [t0,t1,t2,t3,t135,t262]
def v473 := [t0,t1,t2,t3,t135,t4,t262]
def v474 := [t76,t0,t1,t2,t3,t4,t262]
def v475 := [t0,t1,t2,t3,t136,t4,t262]
def v476 := [t0,t137,t1,t2,t3,t4,t262]
def v477 := [t0,t1,t2,t138,t3,t4,t262]
def v478 := [t139,t0,t1,t2,t3,t4,t262]
def v479 := [t0,t1,t2,t140,t3,t4,t262]
def v480 := [t0,t158,t1,t2,t3,t4,t262]
def v481 := [t0,t1,t159,t2,t3,t4,t262]
def t267 := 0x4000122000030070ccc000
def v482 := [t0,t267,t1,t2,t3,t4,t262]
def t268 := 0xee25ebbb9173f9f7ffffcfc
def v483 := [t0,t1,t2,t3,t4,t262,t268]
def t269 := 0x54011117000300000cfc
def v484 := [t269,t0,t1,t2,t3,t4,t262]
def t270 := 0xea20aa888003c9c0f333000
def v485 := [t0,t1,t2,t3,t4,t270,t262]
def v486 := [t163,t0,t1,t2,t3,t4,t262]
def v487 := [t0,t1,t2,t3,t4,t164,t262]
def v488 := [t0,t185,t1,t2,t3,t4,t262]
def v489 := [t0,t1,t2,t3,t186,t4,t262]
def v490 := [t0,t245,t1,t2,t3,t4,t262]
def v491 := [t0,t1,t2,t3,t246,t4,t262]
def v492 := [t0,t1,t2,t247,t3,t4,t262]
def v493 := [t0,t1,t248,t2,t3,t4,t262]
def t271 := 0x40000a80000301c03f00000
def v494 := [t0,t1,t2,t271,t3,t4,t262]
def t272 := 0xeef0afeaae83ffc7ffffff0
def v495 := [t0,t1,t2,t3,t4,t262,t272]
def t273 := 0xd004402e8006000000ff0
def v496 := [t0,t273,t1,t2,t3,t4,t262]
def t274 := 0xae20a12a8000f807c0ff000
def v497 := [t0,t1,t2,t3,t274,t4,t262]
def v498 := [t253,t0,t1,t2,t3,t4,t262]
def v499 := [t0,t1,t2,t3,t4,t262,t254]
def v500 := [t0,t1,t2,t255,t3,t4,t262]
def v501 := [t0,t1,t2,t3,t256,t4,t262]
def v502 := [t202,t0,t1,t2,t3,t4,t262]
def v503 := [t0,t1,t2,t3,t4,t262,t178]
def v504 := [t0,t1,t203,t2,t3,t4,t262]
def v505 := [t0,t1,t2,t3,t4,t179,t262]
def v506 := [t0,t1,t7,t2,t3,t4,t262]
def v507 := [t0,t1,t2,t3,t4,t54,t262]
def v508 := [t0,t60,t1,t2,t3,t4,t262]
def v509 := [t0,t1,t2,t3,t177,t4,t262]
def t275 := 0xaa20a0000003f9c7c000000
def v510 := [t0,t1,t2,t3,t275,t4,t262]
def v511 := [t0,t1,t2,t3,t4,t262,t63]
def v512 := [t0,t1,t2,t3,t184,t4,t262]
def t276 := 0x110a0000000006380000000
def v513 := [t0,t1,t276,t2,t3,t4,t262]
def v514 := [t58,t0,t1,t2,t261,t4,t5]
def v515 := [t0,t1,t2,t3,t261,t4,t5]
def v517 := [t58,t0,t1,t2,t3,t261,t4,t5]
def t278 := 0x100040040808c003003
def v518 := [t278,t0,t1,t2,t3,t4,t5]
def v519 := [t278,t58,t0,t1,t2,t3,t4,t5]
def t279 := 0x40900e80288306c03c00cf0
def v520 := [t0,t1,t2,t279,t4,t5]
def v522 := [t58,t0,t1,t2,t279,t4,t5]
def v523 := [t0,t1,t2,t279,t3,t4,t5]
def v525 := [t58,t0,t1,t2,t279,t3,t4,t5]
def t281 := 0x80000303
def v526 := [t281,t0,t1,t2,t3,t4,t5]
def v528 := [t281,t58,t0,t1,t2,t3,t4,t5]
def t283 := 0x11ce14547e2ccf38f3f3f0f
def v530 := [t0,t1,t2,t283,t3,t4,t5]
def v532 := [t58,t0,t1,t2,t283,t3,t4,t5]
def t285 := 0x40104046040900c303000
def v533 := [t285,t0,t1,t2,t3,t4,t5]
def v534 := [t285,t58,t0,t1,t2,t3,t4,t5]
def t286 := 0x118e04143828c63030f0c0c
def v535 := [t0,t1,t286,t2,t3,t4,t5]
def v537 := [t58,t0,t1,t286,t2,t3,t4,t5]
def t288 := 0x8000303000
def v538 := [t288,t0,t1,t2,t3,t4,t5]
def v539 := [t288,t58,t0,t1,t2,t3,t4,t5]
def t289 := 0xee401beac607f908ffff303
def v540 := [t0,t1,t2,t3,t4,t5,t289]
def v541 := [t58,t0,t1,t2,t3,t4,t5,t289]
def t290 := 0x40104046040108c000303
def v542 := [t290,t0,t1,t2,t3,t4,t5]
def v543 := [t290,t58,t0,t1,t2,t3,t4,t5]
def t291 := 0xee000baa8003f0003cfc000
def v544 := [t0,t1,t2,t3,t4,t291,t5]
def v545 := [t58,t0,t1,t2,t3,t4,t291,t5]
def t292 := 0x908c000000
def v546 := [t292,t0,t1,t2,t3,t4,t5]
def t293 := 0x80cc000000
def v547 := [t293,t0,t1,t2,t3,t4,t5]
def v548 := [t292,t58,t0,t1,t2,t3,t4,t5]
def t294 := 0xbb6ab0404607ffffc303303
def v550 := [t0,t1,t2,t3,t4,t294,t5]
def p63_47 : Projection 46 25 := pick [0,1,2,3,4,5,6,7,8,9,10,11,26,27,28,29,30,31,32,33,34,35,36,37,38] rfl (by decide +kernel) (by decide)
def v552 := [t58,t0,t1,t2,t3,t4,t294,t5]
def t296 := 0x401040460400000303303
def v553 := [t296,t0,t1,t2,t3,t4,t5]
def v554 := [t296,t58,t0,t1,t2,t3,t4,t5]
def t297 := 0xbb2aa0000003f6f70000000
def v555 := [t0,t1,t2,t3,t297,t4,t5]
def v557 := [t58,t0,t1,t2,t3,t297,t4,t5]
def v558 := [t58,t59,t2,t3,t4,t5]
def v559 := [t58,t0,t59,t2,t3,t4,t5]
def v560 := [t58,t59,t1,t2,t3,t4,t5]
def v561 := [t58,t0,t59,t1,t2,t3,t4,t5]
def v562 := [t61,t58,t0,t1,t2,t3,t4,t5]
def v563 := [t58,t1,t2,t3,t62,t4,t5]
def v564 := [t58,t0,t1,t2,t3,t62,t4,t5]
def v565 := [t98,t58,t1,t2,t3,t4,t5]
def v566 := [t98,t58,t0,t1,t2,t3,t4,t5]
def v567 := [t58,t0,t1,t2,t99,t3,t4,t5]
def v568 := [t100,t58,t0,t1,t2,t3,t4,t5]
def v569 := [t104,t58,t0,t1,t2,t3,t4,t5]
def v570 := [t58,t0,t1,t2,t101,t3,t4,t5]
def v571 := [t58,t102,t0,t1,t2,t3,t4,t5]
def v572 := [t58,t0,t1,t103,t2,t3,t4,t5]
def v573 := [t58,t0,t1,t2,t3,t4,t5,t105]
def v574 := [t58,t106,t0,t1,t2,t3,t4,t5]
def v575 := [t58,t0,t1,t2,t3,t4,t107,t5]
def v576 := [t108,t58,t0,t1,t2,t3,t4,t5]
def v577 := [t58,t1,t2,t3,t4,t109,t5]
def v578 := [t58,t0,t1,t2,t3,t4,t109,t5]
def v579 := [t58,t122,t1,t2,t3,t4,t5]
def v580 := [t58,t122,t0,t1,t2,t3,t4,t5]
def v581 := [t58,t0,t1,t2,t3,t135,t4,t5]
def v582 := [t76,t58,t0,t1,t2,t3,t4,t5]
def v583 := [t58,t0,t1,t2,t3,t136,t4,t5]
def v584 := [t58,t0,t137,t1,t2,t3,t4,t5]
def v585 := [t58,t0,t1,t2,t138,t3,t4,t5]
def v586 := [t139,t58,t0,t1,t2,t3,t4,t5]
def v587 := [t58,t0,t1,t2,t140,t3,t4,t5]
def v588 := [t58,t0,t158,t1,t2,t3,t4,t5]
def v589 := [t58,t0,t1,t159,t2,t3,t4,t5]
def v590 := [t58,t0,t160,t1,t2,t3,t4,t5]
def v591 := [t58,t0,t1,t2,t3,t4,t5,t141]
def v592 := [t161,t58,t0,t1,t2,t3,t4,t5]
def v593 := [t58,t0,t1,t2,t3,t4,t162,t5]
def v594 := [t163,t58,t0,t1,t2,t3,t4,t5]
def v596 := [t58,t0,t1,t2,t3,t4,t164,t5]
def v597 := [t58,t0,t185,t1,t2,t3,t4,t5]
def v598 := [t58,t0,t1,t2,t3,t186,t4,t5]
def v599 := [t58,t0,t245,t1,t2,t3,t4,t5]
def v600 := [t58,t0,t1,t2,t3,t246,t4,t5]
def v601 := [t58,t0,t1,t2,t247,t3,t4,t5]
def v602 := [t58,t0,t1,t248,t2,t3,t4,t5]
def v603 := [t58,t0,t1,t2,t249,t3,t4,t5]
def v604 := [t58,t0,t1,t2,t3,t4,t5,t250]
def v605 := [t58,t0,t251,t1,t2,t3,t4,t5]
def v606 := [t58,t0,t1,t2,t3,t252,t4,t5]
def v607 := [t253,t58,t0,t1,t2,t3,t4,t5]
def v609 := [t58,t0,t1,t2,t3,t4,t5,t254]
def v610 := [t58,t0,t1,t2,t255,t3,t4,t5]
def v611 := [t58,t0,t1,t2,t3,t256,t4,t5]
def v612 := [t202,t58,t0,t1,t2,t3,t4,t5]
def v614 := [t58,t0,t1,t2,t3,t4,t5,t257]
def v615 := [t58,t0,t1,t203,t2,t3,t4,t5]
def v616 := [t58,t0,t1,t2,t3,t4,t204,t5]
def v617 := [t58,t0,t1,t7,t2,t3,t4,t5]
def v618 := [t58,t0,t1,t2,t3,t4,t54,t5]
def v619 := [t58,t0,t60,t1,t2,t3,t4,t5]
def v620 := [t58,t0,t1,t2,t3,t177,t4,t5]
def v621 := [t58,t0,t1,t259,t2,t3,t4,t5]
def v622 := [t58,t0,t1,t2,t3,t258,t4,t5]
def v623 := [t58,t0,t1,t2,t3,t4,t5,t63]
def v624 := [t58,t0,t1,t2,t3,t184,t4,t5]
def v625 := [t61,t0,t1,t2,t3,t4,t5]
def v626 := [t0,t1,t2,t3,t62,t4,t5]
def v627 := [t98,t0,t1,t2,t3,t4,t5]
def v628 := [t0,t1,t2,t99,t3,t4,t5]
def v629 := [t100,t0,t1,t2,t3,t4,t5]
def v630 := [t104,t0,t1,t2,t3,t4,t5]
def v631 := [t0,t1,t2,t101,t3,t4,t5]
def v632 := [t6,t0,t1,t2,t101,t3,t4,t5]
def v633 := [t0,t59,t1,t2,t101,t3,t4,t5]
def v634 := [t61,t0,t1,t2,t101,t3,t4,t5]
def v635 := [t0,t1,t2,t101,t3,t62,t4,t5]
def v636 := [t98,t0,t1,t2,t101,t3,t4,t5]
def v637 := [t0,t1,t2,t101,t99,t3,t4,t5]
def v638 := [t100,t1,t101,t3,t4,t5]
def v640 := [t100,t0,t1,t101,t3,t4,t5]
def v642 := [t100,t1,t2,t101,t3,t4,t5]
def v644 := [t100,t0,t1,t2,t101,t3,t4,t5]
def v646 := [t102,t0,t1,t101,t3,t4,t5]
def v647 := [t106,t0,t1,t2,t3,t4,t105]
def v648 := [t102,t0,t1,t2,t101,t3,t4,t5]
def v649 := [t1,t103,t2,t101,t3,t4,t5]
def v651 := [t0,t1,t103,t2,t101,t3,t4,t5]
def v652 := [t0,t1,t103,t2,t3,t4,t5]
def v653 := [t0,t185,t1,t2,t3,t4,t5]
def v654 := [t104,t0,t1,t2,t101,t3,t4,t5]
def v655 := [t1,t2,t101,t3,t4,t5,t105]
def v657 := [t0,t1,t2,t101,t3,t4,t5,t105]
def v658 := [t106,t1,t2,t101,t3,t4,t5]
def v659 := [t106,t0,t1,t2,t101,t3,t4,t5]
def v660 := [t0,t1,t2,t101,t3,t4,t107,t5]
def v661 := [t108,t0,t1,t2,t101,t3,t4,t5]
def v662 := [t0,t1,t2,t101,t3,t4,t109,t5]
def v663 := [t122,t0,t1,t2,t101,t3,t4,t5]
def v664 := [t0,t1,t2,t101,t3,t135,t4,t5]
def v665 := [t76,t0,t1,t2,t101,t3,t4,t5]
def v666 := [t0,t1,t2,t101,t3,t136,t4,t5]
def v667 := [t0,t137,t1,t2,t101,t3,t4,t5]
def v668 := [t0,t1,t2,t101,t138,t3,t4,t5]
def v669 := [t139,t0,t1,t2,t101,t3,t4,t5]
def v670 := [t0,t1,t2,t101,t140,t3,t4,t5]
def v671 := [t0,t158,t1,t2,t101,t3,t4,t5]
def v672 := [t0,t1,t159,t2,t101,t3,t4,t5]
def t299 := 0x500111130003400ccccc
def v673 := [t299,t0,t1,t2,t3,t4,t5]
def v674 := [t299,t0,t1,t2,t101,t3,t4,t5]
def v675 := [t0,t1,t2,t101,t222,t3,t4,t5]
def t300 := 0x4004122004030030c00030
def v676 := [t0,t300,t1,t2,t3,t4,t5]
def v677 := [t0,t300,t1,t2,t101,t3,t4,t5]
def t301 := 0x11ca14446e0ccf08f333303
def v678 := [t0,t1,t2,t301,t3,t4,t5]
def v679 := [t0,t1,t2,t301,t101,t3,t4,t5]
def v680 := [t0,t160,t1,t2,t101,t3,t4,t5]
def v681 := [t0,t1,t2,t101,t3,t4,t5,t141]
def v682 := [t161,t0,t1,t2,t101,t3,t4,t5]
def v683 := [t0,t1,t2,t101,t3,t4,t162,t5]
def v684 := [t163,t0,t1,t2,t101,t3,t4,t5]
def v686 := [t0,t1,t2,t101,t3,t4,t164,t5]
def v687 := [t100,t1,t101,t3,t4,t164,t5]
def v688 := [t163,t0,t2,t101,t3,t164,t5]
def t302 := 0x307c00c00cf0
def v689 := [t302,t0,t1,t2,t101,t4,t5]
def t303 := 0xbf2fe1331170f83fc0cc00c
def v690 := [t0,t1,t2,t101,t4,t303,t5]
def t304 := 0xc80033ff000
def v691 := [t304,t0,t1,t2,t3,t4,t164]
def t305 := 0x11cf14557f3c073cc000fcf
def v692 := [t0,t1,t2,t305,t3,t4,t164]
def t306 := 0x110f00111130cf3cc0ccccc
def v693 := [t0,t1,t306,t2,t3,t4,t5]
def t307 := 0xbfeff5777f7ffffffffffff
def v694 := [t0,t1,t2,t3,t4,t307,t5]
def t308 := 0xc014446e0c00003333303
def v695 := [t0,t308,t1,t2,t3,t4,t5]
def t309 := 0xae20e122004330c30c00030
def v696 := [t0,t1,t2,t3,t309,t4,t5]
def v697 := [t0,t185,t1,t2,t101,t3,t4,t5]
def v698 := [t0,t1,t2,t101,t3,t186,t4,t5]
def v699 := [t0,t245,t1,t2,t101,t3,t4,t5]
def v700 := [t0,t1,t2,t101,t3,t246,t4,t5]
def v701 := [t0,t1,t2,t101,t247,t3,t4,t5]
def v702 := [t0,t1,t248,t2,t101,t3,t4,t5]
def t310 := 0xc004402e0007003300fc0
def v703 := [t0,t310,t1,t2,t3,t4,t5]
def v704 := [t0,t310,t1,t2,t101,t3,t4,t5]
def t311 := 0x51df1ed57fbfcffcfffffff
def v705 := [t0,t1,t2,t3,t311,t4,t5]
def v706 := [t0,t1,t2,t101,t3,t311,t4,t5]
def t312 := 0x40100a80008300c00c00030
def v707 := [t0,t1,t2,t312,t3,t4,t5]
def v708 := [t0,t1,t2,t101,t312,t3,t4,t5]
def t313 := 0x110f1015513cc83cc0ff00f
def v709 := [t0,t1,t313,t2,t3,t4,t5]
def v710 := [t0,t1,t313,t2,t101,t3,t4,t5]
def v711 := [t0,t1,t2,t101,t249,t3,t4,t5]
def v712 := [t0,t1,t2,t101,t3,t4,t5,t250]
def v713 := [t0,t251,t1,t2,t101,t3,t4,t5]
def v714 := [t0,t1,t2,t101,t3,t252,t4,t5]
def v715 := [t253,t0,t1,t2,t101,t3,t4,t5]
def v716 := [t0,t1,t2,t101,t3,t4,t5,t254]
def v717 := [t0,t1,t2,t101,t255,t3,t4,t5]
def v718 := [t0,t1,t2,t101,t3,t256,t4,t5]
def v719 := [t102,t0,t1,t2,t3,t4,t5]
def v720 := [t106,t0,t1,t2,t3,t4,t5]
def v721 := [t202,t0,t1,t2,t101,t3,t4,t5]
def v723 := [t0,t1,t101,t3,t4,t5,t257]
def v724 := [t0,t1,t2,t3,t4,t105,t257]
def v725 := [t0,t1,t2,t101,t3,t4,t5,t257]
def v726 := [t0,t1,t203,t101,t3,t4,t5]
def v728 := [t0,t1,t203,t2,t101,t3,t4,t5]
def v729 := [t0,t1,t2,t101,t3,t4,t204,t5]
def v731 := [t0,t1,t7,t2,t101,t3,t4,t5]
def v732 := [t0,t1,t101,t3,t4,t54,t5]
def v733 := [t0,t1,t2,t101,t3,t4,t54,t5]
def v734 := [t0,t60,t1,t101,t3,t4,t5]
def v735 := [t0,t60,t1,t2,t101,t3,t4,t5]
def v736 := [t0,t1,t2,t101,t3,t177,t4,t5]
def v737 := [t304,t0,t1,t2,t3,t4]
def v739 := [t304,t0,t1,t2,t101,t3,t4]
def v741 := [t304,t0,t1,t2,t3,t4,t5]
def v743 := [t304,t0,t1,t2,t101,t3,t4,t5]
def t314 := 0xffcf1fffff3fff3cfffffcf
def v745 := [t0,t1,t2,t3,t4,t5,t314]
def v746 := [t0,t1,t2,t101,t3,t4,t5,t314]
def v747 := [t0,t1,t2,t305,t3,t4]
def t315 := 0x25fc8b80ff00c
def v749 := [t8,t9,t11,t315,t12]
def v750 := [t13,t8,t9,t11,t315,t12]
def v751 := [t8,t9,t14,t11,t315,t12]
def v752 := [t15,t8,t9,t11,t315,t12]
def v753 := [t8,t16,t9,t11,t315,t12]
def v754 := [t21,t8,t9,t11,t315,t12]
def v755 := [t8,t9,t11,t315,t12,t22]
def v756 := [t23,t8,t9,t11,t315,t12]
def v757 := [t8,t9,t11,t315,t24,t12]
def v758 := [t25,t8,t9,t11,t315,t12]
def v759 := [t8,t9,t11,t315,t26,t12]
def v760 := [t27,t8,t9,t11,t315,t12]
def v761 := [t8,t9,t28,t11,t315,t12]
def v762 := [t19,t8,t9,t11,t315,t12]
def t316 := 0x25fc8b80ffcfc
def v763 := [t8,t9,t11,t315,t316,t12]
def v764 := [t17,t8,t9,t11,t315,t12]
def t317 := 0x2554000023000
def v765 := [t8,t9,t317,t11,t315,t12]
def v766 := [t33,t8,t9,t11,t315]
def v767 := [t33,t8,t9,t11,t315,t12]
def v768 := [t8,t9,t11,t315,t12,t34]
def v769 := [t8,t35,t9,t11,t315]
def v770 := [t8,t35,t9,t11,t315,t12]
def v771 := [t8,t9,t11,t315,t36,t12]
def v772 := [t37,t8,t9,t11,t315,t12]
def v773 := [t8,t9,t11,t315,t38,t12]
def v774 := [t8,t39,t9,t11,t315,t12]
def v775 := [t8,t9,t40,t11,t315,t12]
def t318 := 0x2008803300c
def v776 := [t318,t8,t9,t11,t315,t12]
def t319 := 0x2dfebba4ff3cf
def v777 := [t8,t9,t11,t315,t319,t12]
def t320 := 0x8023024003c3
def v778 := [t8,t320,t9,t11,t315,t12]
def t321 := 0x25dc8300cc000
def v779 := [t8,t9,t11,t321,t315,t12]
def v780 := [t8,t9,t49,t11,t315,t12]
def v781 := [t8,t9,t11,t315,t50]
def v782 := [t8,t9,t11,t315,t12,t50]
def v783 := [t8,t9,t51,t11,t315]
def v784 := [t8,t9,t51,t11,t315,t12]
def v785 := [t8,t52,t9,t11,t315,t12]
def t322 := 0x21c08100e000c
def v786 := [t8,t9,t322,t11,t315,t12]
def t323 := 0x35fdcbd8fff0f
def v787 := [t8,t9,t11,t315,t12,t323]
def t324 := 0x1001405800f03
def v788 := [t8,t9,t324,t11,t315,t12]
def t325 := 0x43c0a801f000
def v789 := [t8,t325,t9,t11,t315,t12]
def v790 := [t8,t9,t48,t11,t315,t12]
def t326 := 0x25fc8b9fff00c
def v791 := [t8,t9,t11,t315,t326,t12]
def v792 := [t45,t8,t9,t11,t315,t12]
def t327 := 0xa88b800000c
def v793 := [t327,t8,t9,t11,t315,t12]
def v794 := [t0,t1,t2,t305,t101,t3,t4]
def v796 := [t0,t1,t2,t305,t3,t4,t5]
def v797 := [t0,t1,t2,t305,t101,t3,t4,t5]
def t328 := 0xee000baa800330000c00000
def v798 := [t0,t1,t2,t3,t4,t328,t5]
def v800 := [t0,t1,t2,t101,t3,t4,t328,t5]
def t330 := 0x110a00000000cf3cc000000
def v801 := [t0,t1,t330,t2,t3,t4,t5]
def v802 := [t0,t1,t330,t2,t101,t3,t4,t5]
def t331 := 0xbbefb4557f3ffffff3fffcf
def v803 := [t0,t1,t2,t3,t4,t331,t5]
def v804 := [t0,t1,t2,t101,t3,t4,t331,t5]
def t332 := 0xc514557f3c000033fffcf
def v805 := [t0,t332,t1,t2,t3,t4,t5]
def v806 := [t0,t332,t1,t2,t101,t3,t4,t5]
def t333 := 0xaa20a000000330c30000000
def v807 := [t0,t1,t2,t3,t333,t4,t5]
def v808 := [t0,t1,t2,t101,t3,t333,t4,t5]
def v809 := [t0,t1,t2,t101,t3,t258,t4,t5]
def v810 := [t0,t1,t2,t101,t3,t4,t5,t63]
def v811 := [t0,t1,t2,t101,t3,t184,t4,t5]
def v813 := [t0,t1,t259,t2,t101,t3,t4,t5]
def v814 := [t104,t106,t1,t2,t3,t4,t5]
def v815 := [t104,t106,t0,t1,t2,t3,t4,t5]
def t334 := 0x100010110000400000cc
def v816 := [t334,t0,t1,t2,t3,t4,t5]
def v817 := [t334,t106,t0,t1,t2,t3,t4,t5]
def t335 := 0x44551735774313fccccfff
def v818 := [t0,t1,t335,t2,t3,t4,t5]
def v819 := [t17,t8,t9,t48,t11,t12]
def v820 := [t19,t8,t9,t48,t11,t12]
def v821 := [t8,t9,t10,t11,t316,t12]
def v822 := [t8,t9,t10,t317,t11,t12]
def v823 := [t8,t9,t10,t48,t26,t12]
def v824 := [t8,t9,t10,t48,t28,t12]
def v825 := [t33,t8,t9,t10,t48,t11]
def v826 := [t8,t35,t9,t10,t48,t11]
def t336 := 0x33000
def v827 := [t336,t8,t9,t10,t11,t12]
def t337 := 0x2d7638a4ff3cf
def v828 := [t8,t9,t10,t11,t337,t12]
def t338 := 0x82238a4003cf
def v829 := [t8,t338,t9,t10,t11,t12]
def v830 := [t8,t9,t48,t11,t12,t46]
def v831 := [t45,t8,t9,t10,t48,t12]
def v832 := [t8,t9,t47,t48,t12]
def v833 := [t8,t9,t47,t10,t48,t12]
def v834 := [t8,t9,t47,t48,t11,t12]
def t339 := 0x21400000e0000
def v835 := [t8,t9,t10,t339,t11,t12]
def v836 := [t8,t9,t10,t48,t11,t235]
def t340 := 0x1081c15800f0f
def v837 := [t8,t9,t340,t10,t11]
def v838 := [t8,t9,t340,t10,t11,t12]
def v839 := [t8,t9,t340,t10,t48,t11]
def v840 := [t8,t9,t10,t48,t11,t50]
def v841 := [t8,t9,t51,t10,t48,t11]
def v842 := [t106,t0,t1,t335,t2,t3,t4,t5]
def v843 := [t290,t106,t0,t1,t2,t3,t4,t5]
def t341 := 0x4044132106030330cccc30
def v844 := [t0,t341,t1,t2,t3,t4,t5]
def v846 := [t106,t0,t341,t1,t2,t3,t4,t5]
def t343 := 0x4000400600010000003c0
def v847 := [t343,t0,t1,t2,t3,t4,t5]
def v848 := [t343,t106,t0,t1,t2,t3,t4,t5]
def t344 := 0x40d11ec16f9707ccff00fff
def v849 := [t0,t1,t2,t3,t344,t4,t5]
def v850 := [t106,t0,t1,t2,t3,t344,t4,t5]
def t345 := 0x110014114000cc00000f
def v851 := [t345,t0,t1,t2,t3,t4,t5]
def v852 := [t345,t106,t0,t1,t2,t3,t4,t5]
def t346 := 0x40900e80288306c03f00c30
def v853 := [t0,t1,t2,t346,t3,t4,t5]
def v854 := [t106,t0,t1,t2,t346,t3,t4,t5]
def v855 := [t100,t106,t0,t1,t2,t3,t4,t5]
def t347 := 0x11cf14557f3cc73cf0f0fcf
def v857 := [t0,t1,t2,t347,t3,t4,t5]
def v858 := [t106,t0,t1,t2,t347,t3,t4,t5]
def t348 := 0x41104147140104c0000c0
def v859 := [t348,t0,t1,t2,t3,t4,t5]
def v860 := [t348,t106,t0,t1,t2,t3,t4,t5]
def v861 := [t106,t0,t1,t103,t2,t3,t4,t5]
def v862 := [t0,t1,t2,t3,t4,t5,t105]
def v863 := [t106,t0,t1,t2,t3,t4,t5,t105]
def t349 := 0x10cc000000
def v864 := [t349,t0,t1,t2,t3,t4,t5]
def v865 := [t349,t106,t0,t1,t2,t3,t4,t5]
def t350 := 0xbb6bb0414717ffffc0003cf
def v866 := [t0,t1,t2,t3,t4,t350,t5]
def v868 := [t106,t0,t1,t2,t3,t4,t350,t5]
def v869 := [t167,t106,t0,t1,t2,t3,t4,t5]
def t352 := 0xbb2aa0000003fef30000000
def v870 := [t0,t1,t2,t3,t352,t4,t5]
def v872 := [t106,t0,t1,t2,t3,t352,t4,t5]
def v873 := [t6,t106,t0,t1,t2,t3,t4,t5]
def v874 := [t106,t0,t59,t1,t2,t3,t4,t5]
def v875 := [t61,t106,t0,t1,t2,t3,t4,t5]
def v876 := [t106,t0,t1,t2,t3,t62,t4,t5]
def v877 := [t98,t106,t0,t1,t2,t3,t4,t5]
def v878 := [t106,t0,t1,t2,t99,t3,t4,t5]
def v879 := [t106,t102,t1,t2,t3,t4,t5]
def v880 := [t106,t102,t0,t1,t2,t3,t4,t5]
def v881 := [t106,t1,t2,t3,t4,t107]
def v882 := [t106,t0,t1,t2,t3,t4,t107]
def v883 := [t106,t1,t2,t3,t4,t107,t5]
def v884 := [t106,t0,t1,t2,t3,t4,t107,t5]
def v885 := [t108,t106,t0,t1,t2,t3,t4,t5]
def v886 := [t106,t0,t1,t2,t3,t4,t109,t5]
def v887 := [t122,t106,t0,t1,t2,t3,t4,t5]
def v888 := [t106,t0,t1,t2,t3,t135,t4,t5]
def v889 := [t76,t106,t0,t1,t2,t3,t4,t5]
def t354 := 0x143
def v890 := [t354,t55,t56,t57]
def v891 := [t106,t0,t1,t2,t3,t136,t4,t5]
def v892 := [t106,t0,t137,t1,t2,t3,t4,t5]
def v893 := [t106,t0,t1,t2,t138,t3,t4,t5]
def v894 := [t139,t106,t0,t1,t2,t3,t4,t5]
def v895 := [t106,t0,t1,t2,t140,t3,t4,t5]
def v896 := [t106,t0,t158,t1,t2,t3,t4,t5]
def v897 := [t106,t0,t1,t159,t2,t3,t4,t5]
def v898 := [t106,t0,t160,t1,t2,t3,t4,t5]
def v899 := [t106,t0,t1,t2,t3,t4,t5,t141]
def v900 := [t161,t106,t0,t1,t2,t3,t4,t5]
def v901 := [t106,t0,t1,t2,t3,t4,t162,t5]
def v902 := [t163,t106,t0,t1,t2,t3,t4,t5]
def v904 := [t106,t0,t1,t2,t3,t4,t164,t5]
def v905 := [t106,t0,t185,t1,t2,t3,t4,t5]
def v906 := [t106,t0,t1,t2,t3,t186,t4,t5]
def v907 := [t106,t0,t245,t1,t2,t3,t4,t5]
def v908 := [t106,t0,t1,t2,t3,t246,t4,t5]
def v909 := [t106,t0,t1,t2,t247,t3,t4,t5]
def v910 := [t106,t0,t1,t248,t2,t3,t4,t5]
def v911 := [t106,t0,t1,t2,t249,t3,t4,t5]
def v912 := [t106,t0,t1,t2,t3,t4,t5,t250]
def v913 := [t106,t0,t251,t1,t2,t3,t4,t5]
def v914 := [t106,t0,t1,t2,t3,t252,t4,t5]
def v915 := [t253,t106,t0,t1,t2,t3,t4,t5]
def v916 := [t106,t0,t1,t2,t3,t4,t5,t254]
def v917 := [t106,t0,t1,t2,t255,t3,t4,t5]
def v918 := [t106,t0,t1,t2,t3,t256,t4,t5]
def v919 := [t202,t106,t0,t1,t2,t3,t4]
def v921 := [t202,t106,t0,t1,t2,t3,t4,t5]
def v923 := [t106,t0,t1,t2,t3,t4,t5,t257]
def v924 := [t106,t0,t1,t203,t2,t3,t4]
def v925 := [t106,t0,t1,t203,t2,t3,t4,t5]
def v926 := [t106,t0,t1,t2,t3,t4,t204,t5]
def v927 := [t106,t0,t1,t7,t2,t3,t4,t5]
def v928 := [t106,t0,t60,t1,t2,t3,t4,t5]
def v929 := [t106,t0,t1,t2,t3,t177,t4,t5]
def v930 := [t106,t0,t1,t2,t3,t258,t4,t5]
def v931 := [t106,t0,t1,t2,t3,t4,t5,t63]
def v932 := [t106,t0,t1,t2,t3,t184,t4,t5]
def v933 := [t106,t0,t1,t259,t2,t3,t4,t5]
def v934 := [t0,t1,t2,t3,t4,t107,t5]
def v935 := [t108,t0,t1,t2,t3,t4,t5]
def v936 := [t108,t122,t1,t2,t3,t4,t5]
def v937 := [t122,t0,t1,t2,t3,t4,t5]
def v938 := [t108,t122,t0,t1,t2,t3,t4,t5]
def t355 := 0x40000000
def v939 := [t355,t0,t1,t2,t3,t4,t5]
def v940 := [t355,t108,t0,t1,t2,t3,t4,t5]
def t356 := 0x8000000000
def v941 := [t356,t108,t0,t1,t2,t3,t4,t5]
def t357 := 0x40541331170393fcccccfc
def v942 := [t0,t357,t2,t3,t4,t5]
def v943 := [t6,t0,t1,t2,t3,t4,t183]
def v944 := [t0,t1,t53,t2,t3,t4,t183]
def v945 := [t58,t0,t1,t2,t3,t4,t183]
def v946 := [t0,t59,t1,t2,t3,t4,t183]
def v947 := [t61,t0,t1,t2,t3,t4,t183]
def v948 := [t0,t1,t2,t3,t62,t4,t183]
def v949 := [t98,t0,t1,t2,t3,t4,t183]
def v950 := [t0,t1,t2,t99,t3,t4,t183]
def v951 := [t100,t0,t1,t2,t3,t4,t183]
def v952 := [t0,t1,t2,t101,t3,t4,t183]
def v953 := [t102,t0,t1,t2,t3,t4,t183]
def v954 := [t0,t1,t103,t2,t3,t4,t183]
def v955 := [t165,t0,t1,t2,t3,t4,t183]
def v956 := [t167,t0,t1,t2,t3,t4,t183]
def v957 := [t0,t1,t2,t3,t4,t107,t183]
def v958 := [t108,t0,t1,t2,t3,t4,t183]
def v959 := [t0,t1,t2,t3,t109,t183]
def v960 := [t0,t1,t2,t3,t4,t109,t183]
def v961 := [t122,t0,t1,t2,t3,t4,t183]
def v962 := [t0,t1,t2,t3,t135,t183]
def v963 := [t0,t1,t2,t3,t135,t4,t183]
def v964 := [t76,t0,t1,t2,t3,t4,t183]
def v965 := [t0,t1,t2,t3,t136,t4,t183]
def v966 := [t0,t137,t1,t2,t3,t4,t183]
def v967 := [t0,t1,t2,t138,t3,t4,t183]
def v968 := [t139,t0,t1,t2,t3,t4,t183]
def v969 := [t0,t1,t2,t140,t3,t4,t183]
def v970 := [t0,t158,t1,t2,t3,t4,t183]
def v971 := [t0,t1,t159,t2,t3,t4,t183]
def t358 := 0x4000122000030040ccc000
def v972 := [t0,t358,t1,t2,t3,t4,t183]
def t359 := 0xee054bbb9173f93fffffcfc
def v973 := [t0,t1,t2,t3,t4,t183,t359]
def t360 := 0x54011117000330000cfc
def v974 := [t360,t0,t1,t2,t3,t4,t183]
def t361 := 0xea000a888003c908f333000
def v975 := [t0,t1,t2,t3,t4,t361,t183]
def v976 := [t163,t0,t1,t2,t3,t4,t183]
def v977 := [t0,t1,t2,t3,t4,t164,t183]
def v978 := [t0,t185,t1,t2,t3,t4,t183]
def v979 := [t0,t1,t2,t3,t186,t4,t183]
def v980 := [t0,t245,t1,t2,t3,t4,t183]
def v981 := [t0,t1,t2,t3,t246,t4,t183]
def v982 := [t0,t1,t2,t247,t3,t4,t183]
def v983 := [t0,t1,t248,t2,t3,t4,t183]
def t362 := 0x40000a80000301003f00000
def v984 := [t0,t1,t2,t362,t3,t4,t183]
def t363 := 0xeed00feaae83ffccffffff0
def v985 := [t0,t1,t2,t3,t4,t183,t363]
def t364 := 0xd004402e8006c00000ff0
def v986 := [t0,t364,t1,t2,t3,t4,t183]
def t365 := 0xae00012a8000f80cc0ff000
def v987 := [t0,t1,t2,t3,t365,t4,t183]
def v988 := [t253,t0,t1,t2,t3,t4,t183]
def v989 := [t0,t1,t2,t3,t4,t183,t254]
def v990 := [t0,t1,t2,t255,t3,t4,t183]
def v991 := [t0,t1,t2,t3,t256,t4,t183]
def t366 := 0xc00830f0000
def v992 := [t366,t0,t1,t2,t3,t4,t183]
def t367 := 0xff8e0fbeb82bff3cfffff0f
def v993 := [t0,t1,t2,t3,t4,t183,t367]
def t368 := 0x118e0414382806300000f0f
def v994 := [t0,t1,t368,t2,t3,t4,t183]
def t369 := 0xee000baa80033904cf0f000
def v995 := [t0,t1,t2,t3,t4,t369,t183]
def v996 := [t0,t1,t7,t2,t3,t4,t183]
def v997 := [t0,t1,t2,t3,t4,t54,t183]
def v998 := [t0,t60,t1,t2,t3,t4,t183]
def v999 := [t0,t1,t2,t3,t177,t4,t183]
def v1000 := [t0,t1,t2,t3,t180,t4,t183]
def v1001 := [t0,t1,t2,t3,t184,t4,t183]
def v1002 := [t0,t1,t182,t2,t3,t4,t183]
def v1003 := [t108,t0,t357,t2,t3,t4,t5]
def v1004 := [t0,t1,t357,t2,t3,t4,t5]
def v1005 := [t108,t0,t1,t357,t2,t3,t4,t5]
def v1006 := [t292,t108,t0,t1,t2,t3,t4,t5]
def v1007 := [t293,t108,t0,t1,t2,t3,t4,t5]
def t370 := 0x4054133117030330ccccfc
def v1008 := [t0,t370,t2,t3,t4,t5]
def v1009 := [t108,t0,t370,t2,t3,t4,t5]
def v1010 := [t0,t370,t1,t2,t3,t4,t5]
def v1011 := [t108,t0,t370,t1,t2,t3,t4,t5]
def t371 := 0x1000000000
def v1012 := [t371,t0,t1,t2,t3,t4,t5]
def v1013 := [t371,t108,t0,t1,t2,t3,t4,t5]
def t372 := 0x40d00ec02e830fccff00ff0
def v1014 := [t0,t1,t2,t372,t4,t5]
def v1015 := [t108,t0,t1,t2,t372,t4,t5]
def v1016 := [t0,t1,t2,t3,t372,t4,t5]
def v1017 := [t108,t0,t1,t2,t3,t372,t4,t5]
def t373 := 0x40d00ec02e8306c03f00ff0
def v1018 := [t0,t1,t2,t373,t4,t5]
def v1019 := [t108,t0,t1,t2,t373,t4,t5]
def v1020 := [t0,t1,t2,t373,t3,t4,t5]
def v1021 := [t108,t0,t1,t2,t373,t3,t4,t5]
def t374 := 0x80000000
def v1022 := [t374,t0,t1,t2,t3,t4,t5]
def v1023 := [t374,t108,t0,t1,t2,t3,t4,t5]
def t375 := 0x118e04143828cf3cf0f0f0f
def v1024 := [t0,t1,t375,t3,t4,t5]
def v1025 := [t108,t0,t1,t375,t3,t4,t5]
def v1026 := [t0,t1,t2,t375,t3,t4,t5]
def v1027 := [t108,t0,t1,t2,t375,t3,t4,t5]
def t376 := 0x904c000000
def v1028 := [t376,t0,t1,t2,t3,t4,t5]
def v1029 := [t376,t108,t0,t1,t2,t3,t4,t5]
def t377 := 0x118e04143828c63030f0f0f
def v1030 := [t0,t1,t377,t3,t4,t5]
def v1031 := [t108,t0,t1,t377,t3,t4,t5]
def v1032 := [t0,t1,t377,t2,t3,t4,t5]
def v1033 := [t108,t0,t1,t377,t2,t3,t4,t5]
def v1034 := [t356,t0,t1,t2,t3,t4,t5]
def v1035 := [t0,t1,t2,t3,t4,t5,t183]
def v1036 := [t108,t0,t1,t2,t3,t4,t5,t183]
def v1037 := [t349,t108,t0,t1,t2,t3,t4,t5]
def t378 := 0xee000baa8003f0003fff000
def v1038 := [t0,t1,t2,t3,t4,t378]
def v1039 := [t108,t0,t1,t2,t3,t4,t378]
def v1040 := [t0,t1,t2,t3,t4,t378,t5]
def v1041 := [t108,t0,t1,t2,t3,t4,t378,t5]
def v1042 := [t108,t0,t1,t2,t3,t135,t5]
def v1043 := [t0,t1,t2,t3,t135,t4,t5]
def v1044 := [t108,t0,t1,t2,t3,t135,t4,t5]
def v1045 := [t108,t6,t0,t1,t2,t3,t4,t5]
def v1046 := [t108,t0,t1,t7,t2,t3,t4,t5]
def v1047 := [t108,t0,t59,t1,t2,t3,t4,t5]
def v1048 := [t108,t61,t0,t1,t2,t3,t4,t5]
def v1049 := [t108,t0,t1,t2,t3,t62,t4,t5]
def v1050 := [t108,t98,t0,t1,t2,t3,t4,t5]
def v1051 := [t108,t0,t1,t2,t99,t3,t4,t5]
def v1052 := [t100,t108,t0,t1,t2,t3,t4,t5]
def v1053 := [t104,t108,t0,t1,t2,t3,t4,t5]
def v1054 := [t108,t102,t0,t1,t2,t3,t4,t5]
def v1055 := [t108,t0,t1,t103,t2,t3,t4,t5]
def v1056 := [t108,t0,t1,t2,t3,t4,t5,t105]
def v1057 := [t108,t0,t1,t2,t3,t4,t107,t5]
def v1058 := [t108,t1,t2,t3,t109,t5]
def t379 := 0x330
def t380 := 0x54cdcc
def t381 := 0xbb5fff
def t382 := 0xe0ae0f
def v1059 := [t379,t380,t381,t382]
def t383 := 0x100
def v1060 := [t383,t379,t380,t381,t382]
def t384 := 0x54cffc
def v1061 := [t379,t384,t381,t382]
def v1062 := [t379,t380,t384,t381,t382]
def t385 := 0x230
def v1063 := [t385,t379,t380,t381,t382]
def t386 := 0x54cccc
def v1064 := [t379,t386,t381,t382]
def v1065 := [t379,t386,t380,t381,t382]
def t387 := 0x200
def v1066 := [t387,t379,t380,t381,t382]
def t388 := 0xe0af3f
def v1067 := [t379,t380,t381,t388]
def v1068 := [t379,t380,t381,t382,t388]
def t389 := 0x130
def v1069 := [t389,t379,t380,t381,t382]
def t390 := 0xe0ac0f
def v1070 := [t379,t380,t381,t390]
def v1071 := [t379,t380,t381,t390,t382]
def t391 := 0xbb5ccf
def v1072 := [t380,t391,t382]
def v1073 := [t379,t380,t391,t382]
def v1074 := [t380,t391,t381,t382]
def v1075 := [t379,t380,t391,t381,t382]
def t392 := 0x408c0c
def v1076 := [t379,t392,t380,t381,t382]
def t393 := 0xf4efcf
def v1077 := [t379,t380,t381,t382,t393]
def t394 := 0x1441c0
def v1078 := [t379,t394,t380,t381,t382]
def t395 := 0xa02203
def v1079 := [t379,t380,t395,t381,t382]
def t396 := 0x104dcc
def v1080 := [t379,t396,t381,t382]
def v1081 := [t379,t396,t380,t381,t382]
def t397 := 0xffdfff
def v1082 := [t379,t380,t381,t382,t397]
def t398 := 0x448000
def v1083 := [t379,t398,t380,t381,t382]
def t399 := 0xab1233
def v1084 := [t379,t399,t381,t382]
def v1085 := [t379,t380,t399,t381,t382]
def t400 := 0xa00e0f
def v1086 := [t379,t380,t400,t381]
def v1087 := [t379,t380,t400,t381,t382]
def t401 := 0xfbffff
def v1088 := [t379,t380,t381,t382,t401]
def t402 := 0x40a000
def v1089 := [t379,t402,t380,t381,t382]
def t403 := 0x1b51f0
def v1090 := [t379,t403,t380,t381]
def v1091 := [t379,t403,t380,t381,t382]
def p63_39 : Projection 46 12 := pick [0,1,2,3,26,27,28,29,30,31,32,33] rfl (by decide +kernel) (by decide)
def v1092 := [t108,t0,t1,t2,t3,t109,t5]
def v1093 := [t108,t1,t2,t3,t4,t109,t5]
def v1094 := [t108,t0,t1,t2,t3,t4,t109,t5]
def v1095 := [t76,t108,t0,t1,t2,t3,t4,t5]
def v1096 := [t108,t0,t1,t2,t3,t136,t4,t5]
def v1097 := [t108,t0,t1,t2,t3,t4,t5,t257]
def v1098 := [t108,t0,t137,t1,t2,t3,t4,t5]
def v1099 := [t108,t0,t1,t2,t138,t3,t4,t5]
def v1100 := [t108,t139,t0,t1,t2,t3,t4,t5]
def v1101 := [t108,t0,t1,t2,t140,t3,t4,t5]
def v1102 := [t108,t0,t158,t1,t2,t3,t4,t5]
def v1103 := [t108,t0,t1,t159,t2,t3,t4,t5]
def v1104 := [t108,t0,t160,t1,t2,t3,t4,t5]
def v1105 := [t108,t0,t1,t2,t3,t4,t5,t141]
def v1106 := [t108,t161,t0,t1,t2,t3,t4,t5]
def v1107 := [t108,t0,t1,t2,t3,t4,t162,t5]
def v1108 := [t108,t163,t0,t1,t2,t3,t4,t5]
def v1109 := [t108,t0,t1,t2,t3,t4,t164,t5]
def v1110 := [t108,t0,t185,t1,t2,t3,t4,t5]
def v1111 := [t108,t0,t1,t2,t3,t186,t4,t5]
def v1112 := [t108,t0,t245,t1,t2,t3,t4,t5]
def v1113 := [t108,t0,t1,t2,t3,t246,t4,t5]
def v1114 := [t108,t0,t1,t2,t247,t3,t4,t5]
def v1115 := [t108,t0,t1,t248,t2,t3,t4,t5]
def v1116 := [t108,t0,t1,t2,t249,t3,t4,t5]
def v1117 := [t108,t0,t1,t2,t3,t4,t5,t250]
def v1118 := [t108,t0,t251,t1,t2,t3,t4,t5]
def v1119 := [t108,t0,t1,t2,t3,t252,t4,t5]
def v1120 := [t108,t253,t0,t1,t2,t3,t4,t5]
def v1121 := [t108,t0,t1,t2,t3,t4,t5,t254]
def v1122 := [t108,t0,t1,t2,t255,t3,t4,t5]
def v1123 := [t108,t0,t1,t2,t3,t256,t4,t5]
def v1124 := [t108,t202,t0,t1,t2,t3,t4,t5]
def v1125 := [t108,t0,t1,t203,t2,t3,t4,t5]
def v1126 := [t108,t0,t1,t2,t3,t4,t204,t5]
def v1127 := [t108,t0,t1,t2,t3,t4,t54,t5]
def v1128 := [t108,t0,t60,t1,t2,t3,t4,t5]
def v1129 := [t108,t0,t1,t2,t3,t177,t4,t5]
def v1130 := [t108,t0,t1,t2,t3,t258,t4,t5]
def v1131 := [t108,t0,t1,t2,t3,t4,t5,t63]
def v1132 := [t108,t0,t1,t2,t3,t184,t4,t5]
def v1133 := [t108,t0,t1,t259,t2,t3,t4,t5]
def v1134 := [t0,t1,t2,t3,t4,t109,t5]
def v1135 := [t6,t0,t1,t2,t3,t4,t109,t5]
def v1136 := [t0,t59,t1,t2,t3,t4,t109,t5]
def v1137 := [t61,t0,t1,t2,t3,t4,t109,t5]
def v1138 := [t1,t2,t3,t62,t4,t109,t5]
def v1139 := [t0,t1,t2,t3,t62,t4,t109,t5]
def v1140 := [t98,t1,t2,t3,t4,t109,t5]
def v1141 := [t98,t0,t1,t2,t3,t4,t109,t5]
def v1142 := [t0,t1,t2,t99,t3,t4,t109,t5]
def v1143 := [t100,t0,t1,t2,t3,t4,t109,t5]
def v1144 := [t102,t0,t1,t2,t3,t4,t109,t5]
def v1145 := [t0,t1,t103,t2,t3,t4,t109,t5]
def v1146 := [t104,t0,t1,t2,t3,t4,t109,t5]
def v1147 := [t0,t1,t2,t3,t4,t109,t5,t105]
def v1148 := [t0,t1,t2,t3,t4,t109,t107,t5]
def v1149 := [t122,t0,t1,t2,t3,t109,t5]
def v1150 := [t122,t0,t1,t2,t3,t4,t109,t5]
def v1151 := [t1,t2,t3,t135,t4,t109,t5]
def v1152 := [t0,t1,t2,t3,t135,t4,t109,t5]
def v1153 := [t76,t0,t1,t2,t3,t4,t109,t5]
def v1154 := [t0,t1,t2,t3,t136,t4,t109,t5]
def v1155 := [t0,t137,t1,t2,t3,t4,t109,t5]
def v1156 := [t0,t1,t2,t138,t3,t4,t109,t5]
def v1157 := [t139,t0,t1,t2,t3,t4,t109,t5]
def v1158 := [t0,t1,t2,t140,t3,t4,t109,t5]
def v1159 := [t0,t158,t1,t2,t3,t4,t109,t5]
def v1160 := [t0,t1,t159,t2,t3,t4,t109,t5]
def v1161 := [t0,t160,t1,t2,t3,t4,t109,t5]
def v1162 := [t0,t1,t2,t3,t4,t109,t5,t141]
def v1163 := [t161,t0,t1,t2,t3,t4,t109,t5]
def v1164 := [t0,t1,t2,t3,t4,t109,t162,t5]
def v1165 := [t163,t0,t1,t2,t3,t4,t109,t5]
def v1166 := [t0,t1,t2,t3,t4,t109,t164,t5]
def v1167 := [t0,t185,t1,t2,t3,t4,t109,t5]
def v1168 := [t0,t1,t2,t3,t186,t4,t109,t5]
def t404 := 0x1000101103037000c0cc
def v1169 := [t404,t0,t1,t2,t3,t4,t5]
def t405 := 0x110a00000000c638000030f
def v1170 := [t0,t1,t405,t2,t3,t4,t5]
def v1171 := [t404,t0,t1,t2,t3,t4,t109,t5]
def v1172 := [t0,t1,t2,t3,t4,t109,t242,t5]
def t406 := 0x4044132106000000cc0c30
def v1173 := [t0,t406,t1,t2,t3,t4,t5]
def v1174 := [t0,t406,t1,t2,t3,t4,t109,t5]
def t407 := 0xbb6ab0404607cfc8c303303
def v1175 := [t0,t1,t2,t3,t4,t407,t5]
def t408 := 0x116bb041471407ffc0003cf
def v1176 := [t0,t1,t408,t2,t3,t4,t5]
def v1177 := [t0,t1,t2,t3,t4,t407,t109,t5]
def v1178 := [t0,t245,t1,t2,t3,t4,t109,t5]
def v1179 := [t0,t1,t2,t3,t246,t4,t109,t5]
def v1180 := [t0,t1,t2,t247,t3,t4,t109,t5]
def v1181 := [t0,t1,t248,t2,t3,t4,t109,t5]
def v1182 := [t0,t1,t2,t249,t3,t4,t109,t5]
def v1183 := [t0,t1,t2,t3,t4,t109,t5,t250]
def v1184 := [t0,t251,t1,t2,t3,t4,t109,t5]
def v1185 := [t0,t1,t2,t3,t252,t4,t109,t5]
def v1186 := [t253,t0,t1,t2,t3,t4,t109,t5]
def v1187 := [t0,t1,t2,t3,t4,t109,t5,t254]
def v1188 := [t0,t1,t2,t255,t3,t4,t109,t5]
def v1189 := [t0,t1,t2,t3,t256,t4,t109,t5]
def t409 := 0x400040060307c003003c0
def v1190 := [t409,t0,t1,t2,t3,t4,t5]
def v1191 := [t409,t0,t1,t2,t3,t4,t109,t5]
def t410 := 0xfbfbbec16f97ffffff0ffff
def v1192 := [t0,t1,t2,t3,t4,t5,t410]
def v1193 := [t0,t1,t2,t3,t4,t109,t5,t410]
def t411 := 0x40900e80288000003c00c30
def v1194 := [t0,t1,t2,t411,t3,t4,t5]
def v1195 := [t0,t1,t2,t411,t3,t4,t109,t5]
def t412 := 0xbb2bb0014114f83fc00f00f
def v1196 := [t0,t1,t2,t3,t4,t412,t5]
def v1197 := [t0,t1,t2,t3,t4,t412,t109,t5]
def v1198 := [t202,t0,t1,t2,t3,t4,t109,t5]
def v1199 := [t0,t1,t2,t3,t4,t109,t5,t257]
def v1200 := [t0,t1,t203,t2,t3,t4,t109,t5]
def v1201 := [t0,t1,t2,t3,t4,t109,t204,t5]
def v1202 := [t0,t1,t7,t2,t3,t4,t109,t5]
def v1203 := [t0,t1,t2,t3,t4,t109,t54,t5]
def v1204 := [t0,t60,t1,t2,t3,t4,t109,t5]
def v1205 := [t0,t1,t2,t3,t177,t109,t5]
def v1206 := [t0,t1,t2,t3,t177,t4,t109,t5]
def v1207 := [t0,t1,t405,t2,t3,t4,t109,t5]
def v1208 := [t0,t1,t2,t3,t4,t109,t331,t5]
def t413 := 0x8404143828000030f0c00
def v1209 := [t0,t413,t1,t2,t3,t4,t5]
def v1210 := [t0,t413,t1,t2,t3,t4,t109,t5]
def t414 := 0xaa61b041471739c7c30f0c0
def v1211 := [t0,t1,t2,t3,t414,t4,t5]
def v1212 := [t0,t1,t2,t3,t414,t4,t109,t5]
def v1213 := [t0,t1,t2,t3,t258,t4,t109,t5]
def v1214 := [t0,t1,t2,t3,t109,t5,t63]
def v1215 := [t0,t1,t2,t3,t4,t109,t5,t63]
def v1216 := [t0,t1,t2,t3,t184,t4,t109,t5]
def v1217 := [t0,t1,t259,t2,t3,t109,t5]
def v1218 := [t0,t1,t259,t2,t3,t4,t109,t5]
def t415 := 0xaa0000000003f800030f000
def v1219 := [t0,t1,t2,t3,t415,t4,t5]
def v1220 := [t0,t1,t2,t3,t415,t4,t109,t5]
def t416 := 0xff6bbbebc717ffffffff3cf
def v1221 := [t0,t1,t2,t3,t4,t5,t416]
def v1222 := [t0,t1,t2,t3,t4,t109,t5,t416]
def t417 := 0x44000baa800000003cf0000
def v1223 := [t0,t1,t2,t3,t417,t4,t5]
def v1224 := [t0,t1,t2,t3,t417,t4,t109,t5]
def v1225 := [t0,t1,t408,t2,t3,t4,t109,t5]
def t418 := 0x1000101100000000c0cc
def v1226 := [t418,t0,t1,t2,t3,t4,t5]
def v1227 := [t418,t122,t0,t1,t2,t3,t4,t5]
def t419 := 0x4455173577430370fcffff
def v1228 := [t0,t1,t419,t2,t3,t4,t5]
def v1229 := [t122,t0,t1,t419,t2,t3,t4,t5]
def v1230 := [t296,t122,t0,t1,t2,t3,t4,t5]
def t420 := 0x4044132106030370cc0c30
def v1231 := [t0,t420,t1,t2,t3,t4,t5]
def v1233 := [t122,t0,t420,t1,t2,t3,t4,t5]
def t422 := 0x4000400600000003003c0
def v1234 := [t422,t0,t1,t2,t3,t4,t5]
def v1235 := [t422,t122,t0,t1,t2,t3,t4,t5]
def t423 := 0x40d11ec16f9707c03f0ffff
def v1236 := [t0,t1,t2,t3,t423,t4,t5]
def v1237 := [t122,t0,t1,t2,t3,t423,t4,t5]
def t424 := 0x1100141140000000f00f
def v1238 := [t424,t0,t1,t2,t3,t4,t5]
def v1239 := [t424,t122,t0,t1,t2,t3,t4,t5]
def t425 := 0x40900e80288307c03c00c30
def v1240 := [t0,t1,t2,t425,t3,t4,t5]
def v1241 := [t122,t0,t1,t2,t425,t3,t4,t5]
def t426 := 0x30f
def v1242 := [t426,t0,t1,t2,t3,t4,t5]
def v1244 := [t426,t122,t0,t1,t2,t3,t4,t5]
def t428 := 0x11cf14557f3cc63833fffcf
def v1245 := [t0,t1,t2,t428,t3,t4,t5]
def v1246 := [t122,t0,t1,t2,t428,t3,t4,t5]
def t429 := 0x41104147140000030f0c0
def v1247 := [t429,t0,t1,t2,t3,t4,t5]
def v1248 := [t429,t122,t0,t1,t2,t3,t4,t5]
def t430 := 0x118e04143828c63830f0c00
def v1249 := [t0,t1,t430,t2,t3,t4,t5]
def v1251 := [t122,t0,t1,t430,t2,t3,t4,t5]
def t432 := 0x30f000
def v1252 := [t432,t0,t1,t2,t3,t4,t5]
def v1253 := [t432,t122,t0,t1,t2,t3,t4,t5]
def t433 := 0xee411bebc717f8003fff3cf
def v1254 := [t0,t1,t2,t3,t4,t5,t433]
def v1255 := [t122,t0,t1,t2,t3,t4,t5,t433]
def v1256 := [t167,t122,t0,t1,t2,t3,t4,t5]
def t434 := 0xee000baa8003f8003cf0000
def v1257 := [t0,t1,t2,t3,t4,t434,t5]
def v1258 := [t122,t0,t1,t2,t3,t4,t434,t5]
def v1259 := [t6,t122,t0,t1,t2,t3,t4,t5]
def v1260 := [t122,t0,t59,t1,t2,t3,t4,t5]
def v1261 := [t61,t122,t0,t1,t2,t3,t4,t5]
def v1262 := [t122,t1,t2,t3,t62,t4,t5]
def v1263 := [t122,t0,t1,t2,t3,t62,t4,t5]
def v1264 := [t98,t122,t1,t2,t3,t4,t5]
def v1265 := [t98,t122,t0,t1,t2,t3,t4,t5]
def v1266 := [t122,t0,t1,t2,t99,t3,t4,t5]
def v1267 := [t100,t122,t0,t1,t2,t3,t4,t5]
def v1268 := [t104,t122,t0,t1,t2,t3,t4,t5]
def v1269 := [t122,t102,t0,t1,t2,t3,t4,t5]
def v1270 := [t122,t0,t1,t103,t2,t3,t4,t5]
def v1271 := [t122,t0,t1,t2,t3,t4,t5,t105]
def v1272 := [t122,t0,t1,t2,t3,t4,t107,t5]
def v1273 := [t122,t1,t2,t3,t135,t5]
def t435 := 0x11500f
def t436 := 0xaa0cc0
def v1274 := [t435,t380,t436,t382]
def t437 := 0x10400c
def v1275 := [t437,t435,t380,t436,t382]
def t438 := 0x55ddcf
def v1276 := [t435,t438,t436,t382]
def v1277 := [t435,t380,t438,t436,t382]
def t439 := 0x11003
def v1278 := [t439,t435,t380,t436,t382]
def t440 := 0x448dc0
def v1279 := [t435,t440,t436,t382]
def v1280 := [t435,t440,t380,t436,t382]
def t441 := 0xf
def v1281 := [t441,t435,t380,t436]
def v1282 := [t441,t435,t380,t436,t382]
def t442 := 0xf1fe0f
def v1283 := [t435,t380,t436,t382,t442]
def t443 := 0x115000
def v1284 := [t443,t435,t380,t436]
def v1285 := [t443,t435,t380,t436,t382]
def t444 := 0xe0ae00
def v1286 := [t435,t380,t436,t444,t382]
def v1287 := [t435,t380,t391,t382]
def v1288 := [t380,t436,t391,t382]
def t445 := 0xcc0
def v1289 := [t445,t391,t382]
def v1290 := [t445,t380,t391,t382]
def v1291 := [t445,t436,t391,t382]
def t446 := 0xfecdcc
def v1292 := [t380,t391,t382,t446]
def t447 := 0x54c10c
def v1293 := [t447,t380,t391,t382]
def t448 := 0xaa0000
def v1294 := [t448,t391,t382]
def v1295 := [t380,t448,t391,t382]
def v1296 := [t448,t436,t391,t382]
def t449 := 0x104ccc
def v1297 := [t449,t436,t391,t382]
def t450 := 0xab1003
def v1298 := [t436,t450,t391,t382]
def t451 := 0xa00c00
def v1299 := [t380,t451,t391,t382]
def t452 := 0xeaaecf
def v1300 := [t380,t391,t452]
def v1301 := [t380,t391,t382,t452]
def v1302 := [t380,t436,t391,t452]
def t453 := 0x40a20f
def v1303 := [t453,t380,t391]
def v1304 := [t453,t380,t391,t382]
def v1305 := [t453,t380,t436,t391]
def t454 := 0xa00c0
def v1306 := [t454,t380,t391,t382]
def t455 := 0xa00c0f
def v1307 := [t380,t455,t436,t391]
def t456 := 0x1b50c0
def v1308 := [t456,t380,t436,t391]
def map39_1 : Projection 12 12 := pick [7,6,11,10,5,4,1,0,9,8,3,2] rfl (by decide +kernel) (by decide)
def v1309 := [t435,t380,t436,t391,t382]
def v1310 := [t435,t392,t380,t436,t382]
def v1311 := [t435,t380,t436,t382,t393]
def v1312 := [t435,t394,t380,t436,t382]
def v1313 := [t435,t380,t395,t436,t382]
def v1314 := [t445,t435,t436,t382]
def v1315 := [t445,t435,t380,t436,t382]
def v1316 := [t435,t380,t436,t382,t446]
def v1317 := [t435,t447,t380,t436,t382]
def v1318 := [t435,t448,t436,t382]
def v1319 := [t435,t380,t448,t436,t382]
def v1320 := [t435,t380,t451,t436,t382]
def v1321 := [t435,t380,t436,t452]
def v1322 := [t435,t380,t436,t382,t452]
def v1323 := [t435,t453,t380,t436]
def v1324 := [t435,t453,t380,t436,t382]
def v1325 := [t454,t435,t380,t436,t382]
def v1326 := [t122,t0,t1,t2,t3,t135,t5]
def v1327 := [t122,t1,t2,t3,t135,t4,t5]
def v1328 := [t122,t0,t1,t2,t3,t135,t4,t5]
def v1329 := [t76,t122,t0,t1,t2,t3,t4,t5]
def v1330 := [t122,t0,t1,t2,t3,t136,t4,t5]
def v1331 := [t122,t0,t137,t1,t2,t3,t4,t5]
def v1332 := [t122,t0,t1,t2,t138,t3,t4,t5]
def v1333 := [t139,t122,t0,t1,t2,t3,t4,t5]
def v1334 := [t122,t0,t1,t2,t140,t3,t4,t5]
def v1335 := [t122,t0,t158,t1,t2,t3,t4,t5]
def v1336 := [t122,t0,t1,t159,t2,t3,t4,t5]
def v1337 := [t122,t0,t160,t1,t2,t3,t4,t5]
def v1338 := [t122,t0,t1,t2,t3,t4,t5,t141]
def v1339 := [t161,t122,t0,t1,t2,t3,t4,t5]
def v1340 := [t122,t0,t1,t2,t3,t4,t162,t5]
def v1341 := [t163,t122,t0,t1,t2,t3,t4,t5]
def v1342 := [t122,t0,t1,t2,t3,t4,t164,t5]
def v1343 := [t122,t0,t185,t1,t2,t3,t4,t5]
def v1344 := [t122,t0,t1,t2,t3,t186,t4,t5]
def v1345 := [t122,t0,t245,t1,t2,t3,t4,t5]
def v1346 := [t122,t0,t1,t2,t3,t246,t4,t5]
def v1347 := [t122,t0,t1,t2,t247,t3,t4,t5]
def v1348 := [t122,t0,t1,t248,t2,t3,t4,t5]
def v1349 := [t122,t0,t1,t2,t249,t3,t4,t5]
def v1350 := [t122,t0,t1,t2,t3,t4,t5,t250]
def v1351 := [t122,t0,t251,t1,t2,t3,t4,t5]
def v1352 := [t122,t0,t1,t2,t3,t252,t4,t5]
def v1353 := [t253,t122,t0,t1,t2,t3,t4,t5]
def v1354 := [t122,t0,t1,t2,t3,t4,t5,t254]
def v1355 := [t122,t0,t1,t2,t255,t3,t4,t5]
def v1356 := [t122,t0,t1,t2,t3,t256,t4,t5]
def v1357 := [t202,t122,t0,t1,t2,t3,t4,t5]
def v1359 := [t122,t0,t1,t2,t3,t4,t5,t257]
def v1360 := [t122,t0,t1,t203,t2,t3,t4,t5]
def v1361 := [t122,t0,t1,t2,t3,t4,t204,t5]
def v1362 := [t122,t0,t1,t7,t2,t3,t4,t5]
def v1363 := [t122,t0,t1,t2,t3,t4,t54,t5]
def v1364 := [t122,t0,t60,t1,t2,t3,t4,t5]
def v1365 := [t122,t0,t1,t2,t3,t177,t4,t5]
def v1366 := [t122,t0,t1,t2,t3,t258,t4,t5]
def v1367 := [t122,t0,t1,t2,t3,t4,t5,t63]
def v1368 := [t122,t0,t1,t2,t3,t184,t4,t5]
def v1369 := [t122,t0,t1,t259,t2,t3,t4,t5]
def v1370 := [t76,t0,t1,t2,t3,t4,t5]
def v1371 := [t0,t1,t2,t3,t136,t4,t5]
def v1372 := [t0,t1,t2,t3,t4,t5,t257]
def v1373 := [t6,t0,t1,t2,t3,t4,t5,t257]
def v1374 := [t0,t59,t1,t2,t3,t4,t5,t257]
def v1375 := [t61,t0,t1,t2,t3,t4,t5,t257]
def v1376 := [t0,t1,t2,t3,t62,t4,t5,t257]
def v1377 := [t98,t0,t1,t2,t3,t4,t5,t257]
def v1378 := [t0,t1,t2,t99,t3,t4,t5,t257]
def v1379 := [t100,t0,t1,t2,t3,t4,t5,t257]
def v1380 := [t102,t0,t1,t2,t3,t4,t5,t257]
def v1381 := [t0,t1,t103,t3,t4,t5,t257]
def v1383 := [t0,t1,t103,t2,t3,t4,t5,t257]
def v1384 := [t104,t0,t1,t2,t3,t4,t5,t257]
def v1385 := [t0,t1,t2,t3,t4,t5,t105,t257]
def v1386 := [t0,t1,t2,t3,t4,t107,t257]
def v1387 := [t0,t1,t2,t3,t4,t107,t5,t257]
def t457 := 0x808030f30f
def v1388 := [t457,t0,t1,t2,t3,t4,t5]
def v1389 := [t457,t0,t1,t2,t3,t4,t5,t257]
def v1390 := [t0,t1,t2,t3,t4,t5,t257,t314]
def v1391 := [t348,t0,t1,t2,t3,t4,t5,t257]
def t458 := 0xff8e0fbeb82bf6303cf0c00
def v1392 := [t0,t1,t2,t3,t4,t5,t458]
def v1393 := [t0,t1,t2,t3,t4,t5,t458,t257]
def v1394 := [t0,t1,t2,t3,t135,t4,t5,t257]
def v1395 := [t76,t0,t1,t2,t3,t4,t5,t257]
def v1396 := [t0,t1,t2,t3,t136,t4,t5,t257]
def v1397 := [t0,t137,t1,t2,t3,t4,t5,t257]
def v1398 := [t0,t1,t2,t138,t3,t4,t5,t257]
def v1399 := [t139,t0,t1,t2,t3,t4,t5,t257]
def v1400 := [t0,t1,t2,t140,t3,t4,t5,t257]
def v1401 := [t0,t158,t1,t2,t3,t4,t5,t257]
def v1402 := [t0,t1,t159,t2,t3,t4,t5,t257]
def v1403 := [t0,t160,t1,t2,t3,t4,t5,t257]
def v1404 := [t0,t1,t2,t3,t4,t5,t141,t257]
def v1405 := [t161,t0,t1,t2,t3,t4,t5,t257]
def v1406 := [t0,t1,t2,t3,t4,t162,t5,t257]
def t459 := 0x4040132102030300cccc0c
def v1407 := [t0,t459,t1,t2,t3,t4,t5]
def v1408 := [t0,t459,t1,t2,t3,t4,t5,t257]
def t460 := 0xff8f4fbfb97bfe3f3ffffff
def v1409 := [t0,t1,t2,t3,t4,t5,t460]
def v1410 := [t0,t1,t2,t3,t4,t5,t257,t460]
def t461 := 0x140010150000700000f0
def v1411 := [t461,t0,t1,t2,t3,t4,t5]
def v1412 := [t461,t0,t1,t2,t3,t4,t5,t257]
def t462 := 0xfb8a0e8ca80bce083333303
def v1413 := [t0,t1,t2,t3,t4,t5,t462]
def v1414 := [t0,t1,t2,t3,t4,t5,t462,t257]
def v1415 := [t163,t0,t1,t2,t3,t4,t5,t257]
def v1417 := [t0,t1,t2,t3,t4,t164,t5,t257]
def v1418 := [t0,t185,t1,t2,t3,t4,t5,t257]
def v1419 := [t0,t1,t2,t3,t186,t4,t5,t257]
def v1420 := [t0,t245,t1,t2,t3,t4,t5,t257]
def v1421 := [t0,t1,t2,t3,t246,t4,t5,t257]
def v1422 := [t0,t1,t2,t247,t3,t4,t5,t257]
def v1423 := [t0,t1,t248,t2,t3,t4,t5,t257]
def v1424 := [t0,t1,t2,t249,t3,t4,t5,t257]
def v1425 := [t0,t1,t2,t3,t4,t5,t250,t257]
def v1426 := [t0,t251,t1,t2,t3,t4,t5,t257]
def v1427 := [t0,t1,t2,t3,t252,t4,t5,t257]
def t463 := 0x40800e80280306003f00f00
def v1428 := [t0,t1,t2,t463,t3,t4,t5]
def v1429 := [t0,t1,t2,t463,t3,t4,t5,t257]
def t464 := 0xffde0ffebeabfff83ffffff
def v1430 := [t0,t1,t2,t3,t4,t5,t464]
def v1431 := [t0,t1,t2,t3,t4,t5,t257,t464]
def t465 := 0x500040068001c000000f0
def v1432 := [t0,t465,t1,t2,t3,t4,t5]
def v1433 := [t0,t465,t1,t2,t3,t4,t5,t257]
def t466 := 0xbf0e013e9028f83800ff00f
def v1434 := [t0,t1,t2,t3,t4,t466,t5]
def v1435 := [t0,t1,t2,t3,t4,t466,t5,t257]
def v1436 := [t253,t0,t1,t2,t3,t4,t5,t257]
def v1437 := [t0,t1,t2,t3,t4,t5,t254,t257]
def v1438 := [t0,t1,t2,t255,t3,t4,t5,t257]
def v1439 := [t0,t1,t2,t3,t256,t4,t5,t257]
def v1440 := [t202,t0,t1,t3,t4,t257]
def v1442 := [t202,t0,t1,t2,t3,t4,t257]
def v1444 := [t202,t0,t1,t3,t4,t5,t257]
def v1445 := [t202,t0,t1,t2,t3,t4,t5,t257]
def v1446 := [t0,t1,t203,t2,t3,t4,t257]
def v1448 := [t0,t1,t203,t2,t3,t4,t5,t257]
def v1449 := [t0,t1,t3,t4,t204,t5,t257]
def v1450 := [t0,t1,t2,t3,t4,t204,t5,t257]
def v1451 := [t0,t1,t2,t3,t4,t204,t5]
def v1452 := [t0,t137,t1,t2,t3,t4,t5]
def v1453 := [t0,t1,t7,t2,t3,t4,t5,t257]
def v1454 := [t0,t1,t2,t3,t4,t54,t5,t257]
def v1455 := [t0,t60,t1,t2,t3,t4,t5,t257]
def v1456 := [t0,t1,t2,t3,t177,t4,t5,t257]
def v1457 := [t0,t1,t203,t2,t3,t4,t5]
def v1458 := [t0,t1,t2,t3,t258,t4,t5,t257]
def v1459 := [t0,t1,t2,t3,t4,t5,t63,t257]
def v1460 := [t0,t1,t2,t3,t184,t4,t5,t257]
def v1461 := [t0,t1,t259,t2,t3,t4,t5,t257]
def t467 := 0xbb0a00000003fe380000000
def v1462 := [t0,t1,t2,t3,t467,t4,t5]
def v1463 := [t0,t1,t2,t3,t467,t4,t5,t257]
def v1464 := [t0,t1,t2,t3,t4,t5,t257,t178]
def v1466 := [t0,t1,t2,t3,t206,t4,t5,t257]
def t469 := 0x20a000000001c7c000000
def v1467 := [t469,t0,t1,t2,t3,t4,t5]
def v1468 := [t469,t0,t1,t2,t3,t4,t5,t257]
def v1469 := [t0,t1,t2,t138,t3,t4,t5]
def v1470 := [t139,t0,t1,t2,t3,t4,t5]
def v1471 := [t0,t245,t1,t2,t3,t4,t5]
def v1472 := [t0,t1,t2,t140,t3,t4,t5]
def v1473 := [t6,t0,t1,t2,t140,t3,t4,t5]
def v1474 := [t0,t59,t2,t140,t3,t4,t5]
def v1475 := [t0,t59,t1,t2,t140,t3,t4,t5]
def v1476 := [t61,t0,t1,t2,t140,t3,t4,t5]
def v1477 := [t0,t1,t2,t140,t3,t62,t4,t5]
def v1478 := [t98,t0,t1,t2,t140,t3,t4,t5]
def v1479 := [t0,t1,t2,t140,t99,t3,t4,t5]
def v1480 := [t100,t0,t1,t2,t140,t3,t4,t5]
def v1481 := [t102,t0,t1,t2,t140,t3,t4,t5]
def v1482 := [t0,t1,t103,t2,t140,t3,t4,t5]
def t470 := 0x100010110000c000c3cf
def v1483 := [t470,t0,t1,t2,t3,t4,t5]
def t471 := 0x110a00000000f63f0000000
def v1484 := [t0,t1,t471,t2,t3,t4,t5]
def v1485 := [t470,t0,t1,t2,t140,t3,t4,t5]
def v1486 := [t0,t1,t2,t140,t222,t3,t4,t5]
def v1487 := [t285,t0,t1,t2,t140,t3,t4,t5]
def t472 := 0x158e45363868f6333cf0c30
def v1488 := [t0,t1,t2,t472,t3,t4,t5]
def v1489 := [t0,t1,t2,t472,t140,t3,t4,t5]
def v1490 := [t104,t0,t1,t2,t140,t3,t4,t5]
def v1491 := [t0,t1,t2,t140,t3,t4,t5,t105]
def v1492 := [t0,t1,t2,t140,t3,t4,t107,t5]
def v1493 := [t0,t1,t2,t140,t3,t135,t4,t5]
def v1494 := [t76,t0,t1,t2,t140,t3,t4,t5]
def v1495 := [t0,t1,t2,t140,t3,t136,t4,t5]
def v1496 := [t0,t137,t1,t2,t140,t3,t4,t5]
def v1497 := [t0,t1,t2,t140,t138,t3,t4,t5]
def v1498 := [t139,t0,t140,t3,t4,t5]
def v1500 := [t139,t0,t1,t140,t3,t4,t5]
def v1502 := [t139,t0,t2,t140,t3,t4,t5]
def v1503 := [t139,t0,t1,t2,t140,t3,t4,t5]
def v1504 := [t0,t158,t1,t140,t3,t4,t5]
def v1505 := [t0,t158,t1,t2,t140,t3,t4,t5]
def v1506 := [t0,t159,t2,t140,t3,t4,t5]
def v1507 := [t0,t1,t159,t2,t140,t3,t4,t5]
def v1508 := [t0,t1,t159,t2,t3,t4,t5]
def v1509 := [t0,t160,t1,t2,t140,t3,t4,t5]
def v1510 := [t0,t2,t140,t3,t4,t5,t141]
def p63_31 : Projection 46 26 := pick [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25] rfl (by decide +kernel) (by decide)
def v1513 := [t0,t1,t2,t140,t3,t4,t5,t141]
def v1514 := [t161,t0,t2,t140,t3,t4,t5]
def v1515 := [t161,t0,t1,t2,t140,t3,t4,t5]
def v1516 := [t0,t1,t2,t140,t3,t4,t162,t5]
def v1517 := [t163,t0,t1,t2,t140,t3,t4,t5]
def v1518 := [t0,t1,t2,t140,t3,t4,t164,t5]
def v1519 := [t0,t185,t1,t2,t140,t3,t4,t5]
def v1520 := [t0,t1,t2,t140,t3,t186,t4,t5]
def v1521 := [t0,t245,t1,t2,t140,t3,t4,t5]
def v1522 := [t0,t1,t140,t3,t246,t4,t5]
def v1523 := [t0,t1,t2,t140,t3,t246,t4,t5]
def v1524 := [t0,t1,t2,t140,t247,t3,t4,t5]
def v1525 := [t0,t1,t248,t140,t3,t4,t5]
def v1526 := [t0,t1,t248,t2,t140,t3,t4,t5]
def t473 := 0x800400280006003c00ff0
def v1527 := [t0,t473,t1,t2,t3,t4,t5]
def v1528 := [t0,t473,t1,t2,t140,t3,t4,t5]
def t474 := 0x55df4ff73ffbf7ff3ffcfff
def v1529 := [t0,t1,t2,t3,t474,t4,t5]
def v1530 := [t0,t1,t2,t140,t3,t474,t4,t5]
def t475 := 0x40500ac0068301c00300000
def v1531 := [t0,t1,t2,t475,t3,t4,t5]
def v1532 := [t0,t1,t2,t140,t475,t3,t4,t5]
def t476 := 0x150f41371178f03f00fc00f
def v1533 := [t0,t1,t2,t476,t3,t4,t5]
def v1534 := [t0,t1,t2,t476,t140,t3,t4,t5]
def v1535 := [t0,t1,t2,t140,t249,t3,t4,t5]
def v1536 := [t0,t1,t2,t140,t3,t4,t5,t250]
def v1537 := [t0,t251,t1,t2,t140,t3,t4,t5]
def v1538 := [t0,t1,t2,t140,t3,t252,t4,t5]
def v1539 := [t253,t0,t1,t2,t140,t3,t4,t5]
def v1540 := [t0,t1,t2,t140,t3,t4,t5,t254]
def v1541 := [t0,t1,t2,t140,t255,t3,t4,t5]
def v1542 := [t0,t1,t2,t140,t3,t256,t4,t5]
def v1543 := [t0,t158,t1,t2,t3,t4,t5]
def v1544 := [t202,t0,t1,t2,t140,t3,t4,t5]
def v1545 := [t0,t1,t203,t2,t140,t3,t4,t5]
def v1546 := [t0,t1,t2,t140,t3,t4,t204,t5]
def v1547 := [t0,t1,t7,t2,t140,t3,t4,t5]
def v1548 := [t0,t1,t140,t3,t4,t54,t5]
def v1549 := [t0,t1,t2,t140,t3,t4,t54,t5]
def v1550 := [t0,t60,t1,t140,t3,t4,t5]
def v1551 := [t0,t60,t1,t2,t140,t3,t4,t5]
def v1552 := [t0,t1,t2,t140,t3,t177,t4,t5]
def t477 := 0x40001220000f0003cfc000
def v1553 := [t0,t477,t1,t2,t3,t4,t5]
def v1554 := [t0,t477,t1,t2,t140,t3,t4,t5]
def v1555 := [t0,t1,t2,t140,t3,t4,t5,t460]
def t478 := 0x118f44153978063f0000fff
def v1556 := [t0,t1,t2,t478,t3,t4,t5]
def v1557 := [t0,t1,t2,t478,t140,t3,t4,t5]
def t479 := 0xea000a88800308000303000
def v1558 := [t0,t1,t2,t3,t4,t479,t5]
def v1559 := [t0,t1,t2,t140,t3,t4,t479,t5]
def v1560 := [t0,t1,t471,t2,t140,t3,t4,t5]
def t480 := 0xbfafe537397bfffffcfcfff
def v1561 := [t0,t1,t2,t3,t4,t480,t5]
def v1562 := [t0,t1,t2,t140,t3,t4,t480,t5]
def t481 := 0x4854537397800003cfcfff
def v1563 := [t0,t1,t481,t2,t3,t4,t5]
def v1564 := [t0,t1,t481,t2,t140,t3,t4,t5]
def t482 := 0xaa20a000000309c0c000000
def v1565 := [t0,t1,t2,t3,t482,t4,t5]
def v1566 := [t0,t1,t2,t140,t3,t482,t4,t5]
def v1567 := [t0,t1,t2,t140,t3,t258,t4,t5]
def v1568 := [t0,t1,t2,t140,t3,t4,t5,t63]
def v1569 := [t0,t1,t2,t140,t3,t184,t4,t5]
def v1570 := [t0,t1,t259,t2,t140,t3,t4,t5]
def v1571 := [t0,t251,t1,t2,t3,t4,t5]
def v1572 := [t0,t160,t1,t2,t3,t4,t5]
def v1573 := [t0,t1,t2,t3,t4,t5,t141]
def v1574 := [t161,t0,t1,t2,t3,t4,t5]
def v1575 := [t0,t1,t2,t3,t4,t162,t5]
def v1576 := [t163,t0,t1,t2,t3,t4,t5]
def v1577 := [t0,t1,t2,t3,t4,t164,t5]
def v1578 := [t0,t1,t2,t3,t186,t4,t5]
def v1579 := [t0,t1,t2,t3,t246,t4,t5]
def v1580 := [t0,t1,t2,t247,t3,t4,t5]
def v1581 := [t0,t1,t248,t2,t3,t4,t5]
def v1582 := [t0,t1,t2,t249,t3,t4,t5]
def v1583 := [t0,t1,t2,t3,t4,t5,t250]
def v1584 := [t0,t1,t2,t3,t252,t4,t5]
def v1585 := [t253,t0,t1,t2,t3,t4,t5]
def v1586 := [t0,t1,t2,t3,t4,t5,t254]
def v1587 := [t0,t1,t2,t255,t3,t4,t5]
def v1588 := [t0,t1,t2,t3,t256,t4,t5]
def v1589 := [t202,t0,t1,t2,t3,t4,t5]
def v1590 := [t0,t1,t2,t3,t4,t54,t5]
def v1591 := [t0,t1,t2,t3,t177,t4,t5]
def v1592 := [t0,t1,t2,t3,t258,t4,t5]
def v1593 := [t0,t1,t2,t3,t4,t5,t63]
def v1594 := [t0,t1,t2,t3,t184,t4,t5]
def v1595 := [t0,t1,t259,t2,t3,t4,t5]
theorem b0 : Ban 25 5 v4 := checkedSmall
theorem b1 : Ban 25 5 v5 := checkedSmall
theorem b2 : Ban 25 5 v6 := checkedSmall
theorem b3 : Ban 25 5 v7 := checkedSmall
theorem b4 : Ban 25 5 v8 := checkedSmall
theorem b5 : Ban 25 5 v9 := checkedSmall
theorem b6 : Ban 25 5 v10 := checkedSmall
theorem b7 : Ban 25 5 v11 := checkedSmall
theorem b8 : Ban 25 5 v12 := checkedSmall
theorem b9 : Ban 25 5 v13 := checkedSmall
theorem b10 : Ban 25 5 v14 := checkedSmall
theorem b11 : Ban 25 5 v15 := checkedSmall
theorem b12 : Ban 25 5 v16 := checkedSmall
theorem b13 : Ban 25 5 v17 := checkedSmall
theorem b14 : Ban 25 5 v18 := checkedSmall
theorem b15 : Ban 25 5 v19 := checkedSmall
theorem b16 : Ban 25 5 v20 := checkedSmall
theorem b17 : Ban 25 5 v21 := checkedSmall
theorem b18 : Ban 25 5 v22 := checkedSmall
theorem b19 : Ban 25 5 v23 := checkedSmall
theorem b20 : Ban 25 5 v24 := checkedSmall
theorem b21 : Ban 25 5 v25 := checkedSmall
theorem b22 : Ban 25 5 v26 := checkedSmall
theorem b23 : Ban 25 5 v27 := checkedSmall
theorem b24 : Ban 25 5 v28 := checkedSmall
theorem b25 : Ban 25 5 v29 := checkedSmall
theorem b26 : Ban 25 5 v30 := checkedSmall
theorem b27 : Ban 25 5 v31 := checkedSmall
theorem b28 : Ban 25 5 v32 := checkedSmall
theorem b29 : Ban 25 5 v33 := checkedSmall
theorem b30 : Ban 25 5 v34 := checkedSmall
theorem b31 : Ban 25 5 v35 := checkedSmall
theorem b32 : Ban 25 5 v36 := checkedSmall
theorem b33 : Ban 25 5 v37 := checkedSmall
theorem b34 : Ban 25 5 v38 := checkedSmall
theorem b35 : Ban 25 5 v39 := checkedSmall
theorem b36 : Ban 25 5 v40 := checkedSmall
theorem b37 : Ban 25 5 v41 := checkedSmall
theorem b38 : Ban 25 5 v42 := checkedSmall
theorem b39 : Ban 25 5 v43 := checkedSmall
theorem b40 : Ban 25 5 v44 := checkedSmall
theorem b41 : Ban 25 5 v45 := checkedSmall
theorem b42 : Ban 25 5 v46 := checkedSmall
theorem b43 : Ban 25 5 v47 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b44 : Ban 25 6 v3 := viaBranch (ws := [v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,v31,v32,v33,v34,v35,v36,v37,v38,v39,v40,v41,v42,v43,v44,v45,v46,v47]) (consBan b0 (consBan b1 (consBan b2 (consBan b3 (consBan b4 (consBan b5 (consBan b6 (consBan b7 (consBan b8 (consBan b9 (consBan b10 (consBan b11 (consBan b12 (consBan b13 (consBan b14 (consBan b15 (consBan b16 (consBan b17 (consBan b18 (consBan b19 (consBan b20 (consBan b21 (consBan b22 (consBan b23 (consBan b24 (consBan b25 (consBan b26 (consBan b27 (consBan b28 (consBan b29 (consBan b30 (consBan b31 (consBan b32 (consBan b33 (consBan b34 (consBan b35 (consBan b36 (consBan b37 (consBan b38 (consBan b39 (consBan b40 (consBan b41 (consBan b42 (consBan b43 (nilBan 25 5))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b828 : Ban 25 5 v819 := checkedSmall
theorem b829 : Ban 25 5 v820 := checkedSmall
theorem b830 : Ban 25 5 v821 := checkedSmall
theorem b831 : Ban 25 5 v822 := checkedSmall
theorem b832 : Ban 25 5 v823 := checkedSmall
theorem b833 : Ban 25 5 v824 := checkedSmall
theorem b834 : Ban 25 5 v825 := checkedSmall
theorem b835 : Ban 25 5 v826 := checkedSmall
theorem b836 : Ban 25 5 v827 := checkedSmall
theorem b837 : Ban 25 5 v828 := checkedSmall
theorem b838 : Ban 25 5 v829 := checkedSmall
theorem b180 : Ban 25 5 v182 := checkedSmall
theorem b839 : Ban 25 5 v830 := checkedSmall
theorem b840 : Ban 25 5 v831 := checkedSmall
theorem b841 : Ban 25 5 v832 := checkedSmall
theorem b842 : Ban 25 5 v833 := checkedSmall
theorem b843 : Ban 25 5 v834 := checkedSmall
theorem b844 : Ban 25 5 v835 := checkedSmall
theorem b390 : Ban 25 5 v392 := checkedSmall
theorem b391 : Ban 25 5 v393 := checkedSmall
theorem b845 : Ban 25 5 v836 := checkedSmall
theorem b846 : Ban 25 5 v837 := checkedSmall
theorem b847 : Ban 25 5 v838 := checkedSmall
theorem b848 : Ban 25 5 v839 := checkedSmall
theorem b349 : Ban 25 5 v350 := checkedSmall
theorem b849 : Ban 25 5 v840 := checkedSmall
theorem b850 : Ban 25 5 v841 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b851 : Ban 25 6 v41 := viaBranch (ws := [v819,v820,v16,v821,v18,v822,v823,v824,v825,v826,v827,v828,v829,v182,v39,v830,v831,v832,v833,v834,v835,v392,v393,v836,v837,v838,v839,v350,v840,v841,v38]) (consBan b828 (consBan b829 (consBan b12 (consBan b830 (consBan b14 (consBan b831 (consBan b832 (consBan b833 (consBan b834 (consBan b835 (consBan b836 (consBan b837 (consBan b838 (consBan b180 (consBan b35 (consBan b839 (consBan b840 (consBan b841 (consBan b842 (consBan b843 (consBan b844 (consBan b390 (consBan b391 (consBan b845 (consBan b846 (consBan b847 (consBan b848 (consBan b349 (consBan b849 (consBan b850 (consBan b34 (nilBan 25 5)))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w12 : Wide 25 6 v41 := viaSub (ws := [v3,v41]) (consBan b44 (consBan b851 (nilBan 25 6))) (by decide) (by decide +kernel)
theorem b46 : Ban 46 8 v1 := smallByCut p63_61 w12
theorem b48 : Ban 46 7 v49 := smallByCut p63_61 w12
theorem b51 : Ban 6 3 v55 := checkedSmall
theorem b902 : Ban 6 3 v890 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w13 : Wide 6 3 v890 := viaSub (ws := [v55,v890]) (consBan b51 (consBan b902 (nilBan 6 3))) (by decide) (by decide +kernel)
theorem b50 : Ban 46 7 v51 := smallByCut p63_42 w13
theorem b53 : Ban 46 7 v53 := smallByCut p63_21 w13
theorem b54 : Ban 46 7 v56 := smallByCut p63_21 w13
theorem b55 : Ban 46 7 v57 := smallByCut p63_42 w13
theorem b56 : Ban 46 7 v58 := smallByCut p63_42 w13
theorem b57 : Ban 46 7 v59 := smallByCut p63_21 w13
theorem b58 : Ban 46 7 v60 := smallByCut p63_21 w13
theorem b60 : Ban 46 7 v61 := smallByCut p63_21 w13
theorem b61 : Ban 46 7 v63 := smallByCut p63_21 w13
theorem b62 : Ban 26 5 v68 := checkedSmall
theorem b63 : Ban 26 5 v69 := checkedSmall
theorem b64 : Ban 26 5 v70 := checkedSmall
theorem b65 : Ban 26 5 v71 := checkedSmall
theorem b66 : Ban 26 5 v72 := checkedSmall
theorem b67 : Ban 26 5 v73 := checkedSmall
theorem b68 : Ban 26 4 v75 := checkedSmall
theorem b69 : Ban 26 4 v76 := checkedSmall
theorem b70 : Ban 26 4 v77 := checkedSmall
theorem b71 : Ban 26 4 v78 := checkedSmall
theorem b72 : Ban 26 4 v79 := checkedSmall
theorem b73 : Ban 26 4 v80 := checkedSmall
theorem b74 : Ban 26 4 v81 := checkedSmall
theorem b75 : Ban 26 4 v82 := checkedSmall
theorem b76 : Ban 26 4 v83 := checkedSmall
theorem b77 : Ban 26 4 v84 := checkedSmall
theorem b78 : Ban 26 4 v85 := checkedSmall
theorem b79 : Ban 26 4 v86 := checkedSmall
theorem b80 : Ban 26 4 v87 := checkedSmall
theorem b81 : Ban 26 4 v88 := checkedSmall
theorem b82 : Ban 26 4 v89 := checkedSmall
theorem b83 : Ban 26 4 v90 := checkedSmall
theorem b84 : Ban 26 4 v91 := checkedSmall
theorem b85 : Ban 26 4 v92 := checkedSmall
theorem b86 : Ban 26 4 v93 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b87 : Ban 26 5 v74 := viaBranch (ws := [v75,v76,v77,v78,v79,v80,v81,v82,v83,v84,v85,v86,v87,v88,v89,v90,v91,v92,v93]) (consBan b68 (consBan b69 (consBan b70 (consBan b71 (consBan b72 (consBan b73 (consBan b74 (consBan b75 (consBan b76 (consBan b77 (consBan b78 (consBan b79 (consBan b80 (consBan b81 (consBan b82 (consBan b83 (consBan b84 (consBan b85 (consBan b86 (nilBan 26 4)))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b88 : Ban 26 5 v94 := checkedSmall
theorem b89 : Ban 26 5 v95 := checkedSmall
theorem b90 : Ban 26 5 v96 := checkedSmall
theorem b91 : Ban 26 5 v97 := checkedSmall
theorem b92 : Ban 26 5 v98 := checkedSmall
theorem b93 : Ban 26 5 v99 := checkedSmall
theorem b94 : Ban 26 5 v100 := checkedSmall
theorem b95 : Ban 26 5 v101 := checkedSmall
theorem b96 : Ban 26 5 v102 := checkedSmall
theorem b97 : Ban 26 5 v103 := checkedSmall
theorem b98 : Ban 26 5 v104 := checkedSmall
theorem b99 : Ban 26 5 v105 := checkedSmall
theorem b100 : Ban 26 5 v106 := checkedSmall
theorem b101 : Ban 26 5 v107 := checkedSmall
theorem b102 : Ban 26 5 v108 := checkedSmall
theorem b103 : Ban 26 5 v109 := checkedSmall
theorem b104 : Ban 26 5 v110 := checkedSmall
theorem b105 : Ban 26 5 v111 := checkedSmall
theorem b106 : Ban 26 5 v112 := checkedSmall
theorem b107 : Ban 26 5 v113 := checkedSmall
theorem b108 : Ban 26 5 v114 := checkedSmall
theorem b109 : Ban 26 5 v115 := checkedSmall
theorem b110 : Ban 26 5 v116 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b111 : Ban 26 6 v67 := viaBranch (ws := [v68,v69,v70,v71,v72,v73,v74,v94,v95,v96,v97,v98,v99,v100,v101,v102,v103,v104,v105,v106,v107,v108,v109,v110,v111,v112,v113,v114,v115,v116]) (consBan b62 (consBan b63 (consBan b64 (consBan b65 (consBan b66 (consBan b67 (consBan b87 (consBan b88 (consBan b89 (consBan b90 (consBan b91 (consBan b92 (consBan b93 (consBan b94 (consBan b95 (consBan b96 (consBan b97 (consBan b98 (consBan b99 (consBan b100 (consBan b101 (consBan b102 (consBan b103 (consBan b104 (consBan b105 (consBan b106 (consBan b107 (consBan b108 (consBan b109 (consBan b110 (nilBan 26 5))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b112 : Ban 26 6 v66 := viaPerm map31_4 map31_4 b111 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w2 : Wide 26 6 v66 := viaSub (ws := [v66]) (consBan b112 (nilBan 26 6)) (by decide) (by decide +kernel)
theorem b114 : Ban 46 7 v64 := smallByCut p63_31 w2
theorem b115 : Ban 46 7 v117 := checkedSmall
theorem b337 : Ban 25 5 v338 := checkedSmall
theorem b338 : Ban 25 5 v339 := checkedSmall
theorem b339 : Ban 25 5 v340 := checkedSmall
theorem b340 : Ban 25 5 v341 := checkedSmall
theorem b341 : Ban 25 5 v342 := checkedSmall
theorem b342 : Ban 25 5 v343 := checkedSmall
theorem b343 : Ban 25 5 v344 := checkedSmall
theorem b188 : Ban 25 5 v190 := checkedSmall
theorem b344 : Ban 25 5 v345 := checkedSmall
theorem b345 : Ban 25 5 v346 := checkedSmall
theorem b151 : Ban 25 5 v155 := checkedSmall
theorem b193 : Ban 25 5 v195 := checkedSmall
theorem b346 : Ban 25 5 v347 := checkedSmall
theorem b347 : Ban 25 5 v348 := checkedSmall
theorem b348 : Ban 25 5 v349 := checkedSmall
theorem b350 : Ban 25 5 v351 := checkedSmall
theorem b351 : Ban 25 5 v352 := checkedSmall
theorem b352 : Ban 25 5 v353 := checkedSmall
theorem b353 : Ban 25 5 v354 := checkedSmall
theorem b354 : Ban 25 5 v355 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b355 : Ban 25 6 v47 := viaBranch (ws := [v338,v339,v340,v341,v342,v343,v344,v190,v345,v346,v155,v195,v347,v348,v349,v350,v43,v351,v44,v352,v42,v353,v354,v355]) (consBan b337 (consBan b338 (consBan b339 (consBan b340 (consBan b341 (consBan b342 (consBan b343 (consBan b188 (consBan b344 (consBan b345 (consBan b151 (consBan b193 (consBan b346 (consBan b347 (consBan b348 (consBan b349 (consBan b39 (consBan b350 (consBan b40 (consBan b351 (consBan b38 (consBan b352 (consBan b353 (consBan b354 (nilBan 25 5))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w7 : Wide 25 6 v47 := viaSub (ws := [v3,v47]) (consBan b44 (consBan b355 (nilBan 25 6))) (by decide) (by decide +kernel)
theorem b116 : Ban 46 7 v118 := smallByCut p63_61 w7
theorem b117 : Ban 46 7 v119 := smallByCut p63_42 w13
theorem b118 : Ban 46 7 v120 := smallByCut p63_21 w13
theorem b119 : Ban 46 7 v121 := smallByCut p63_42 w13
theorem b120 : Ban 46 7 v122 := smallByCut p63_42 w13
theorem b121 : Ban 46 7 v123 := smallByCut p63_42 w13
theorem b122 : Ban 46 7 v124 := smallByCut p63_42 w13
theorem b123 : Ban 46 7 v125 := smallByCut p63_42 w13
theorem b124 : Ban 46 7 v126 := smallByCut p63_42 w13
theorem b125 : Ban 46 7 v127 := smallByCut p63_42 w13
theorem b126 : Ban 46 7 v128 := smallByCut p63_42 w13
theorem b127 : Ban 46 7 v129 := smallByCut p63_21 w13
theorem b128 : Ban 25 5 v132 := checkedSmall
theorem b129 : Ban 25 5 v133 := checkedSmall
theorem b130 : Ban 25 5 v134 := checkedSmall
theorem b131 : Ban 25 5 v135 := checkedSmall
theorem b132 : Ban 25 5 v136 := checkedSmall
theorem b133 : Ban 25 5 v137 := checkedSmall
theorem b134 : Ban 25 5 v138 := checkedSmall
theorem b135 : Ban 25 5 v139 := checkedSmall
theorem b136 : Ban 25 5 v140 := checkedSmall
theorem b137 : Ban 25 5 v141 := checkedSmall
theorem b138 : Ban 25 5 v142 := checkedSmall
theorem b139 : Ban 25 5 v143 := checkedSmall
theorem b140 : Ban 25 5 v144 := checkedSmall
theorem b141 : Ban 25 5 v145 := checkedSmall
theorem b142 : Ban 25 5 v146 := checkedSmall
theorem b143 : Ban 25 5 v147 := checkedSmall
theorem b144 : Ban 25 5 v148 := checkedSmall
theorem b145 : Ban 25 5 v149 := checkedSmall
theorem b146 : Ban 25 5 v150 := checkedSmall
theorem b147 : Ban 25 5 v151 := checkedSmall
theorem b148 : Ban 25 5 v152 := checkedSmall
theorem b149 : Ban 25 5 v153 := checkedSmall
theorem b150 : Ban 25 5 v154 := checkedSmall
theorem b152 : Ban 25 5 v156 := checkedSmall
theorem b153 : Ban 25 5 v157 := checkedSmall
theorem b154 : Ban 25 5 v158 := checkedSmall
theorem b155 : Ban 25 5 v159 := checkedSmall
theorem b156 : Ban 25 5 v160 := checkedSmall
theorem b157 : Ban 25 5 v161 := checkedSmall
theorem b158 : Ban 25 5 v162 := checkedSmall
theorem b159 : Ban 25 5 v163 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b160 : Ban 25 6 v31 := viaBranch (ws := [v132,v133,v134,v135,v136,v137,v138,v139,v140,v141,v142,v143,v144,v145,v146,v33,v147,v148,v149,v150,v151,v152,v153,v154,v155,v156,v157,v158,v159,v160,v161,v162,v163,v32]) (consBan b128 (consBan b129 (consBan b130 (consBan b131 (consBan b132 (consBan b133 (consBan b134 (consBan b135 (consBan b136 (consBan b137 (consBan b138 (consBan b139 (consBan b140 (consBan b141 (consBan b142 (consBan b29 (consBan b143 (consBan b144 (consBan b145 (consBan b146 (consBan b147 (consBan b148 (consBan b149 (consBan b150 (consBan b151 (consBan b152 (consBan b153 (consBan b154 (consBan b155 (consBan b156 (consBan b157 (consBan b158 (consBan b159 (consBan b28 (nilBan 25 5))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w3 : Wide 25 6 v31 := viaSub (ws := [v3,v31]) (consBan b44 (consBan b160 (nilBan 25 6))) (by decide) (by decide +kernel)
theorem b162 : Ban 46 7 v130 := smallByCut p63_61 w3
theorem b163 : Ban 46 7 v164 := smallByCut p63_61 w3
theorem b164 : Ban 25 5 v166 := checkedSmall
theorem b165 : Ban 25 5 v167 := checkedSmall
theorem b166 : Ban 25 5 v168 := checkedSmall
theorem b167 : Ban 25 5 v169 := checkedSmall
theorem b168 : Ban 25 5 v170 := checkedSmall
theorem b169 : Ban 25 5 v171 := checkedSmall
theorem b170 : Ban 25 5 v172 := checkedSmall
theorem b171 : Ban 25 5 v173 := checkedSmall
theorem b172 : Ban 25 5 v174 := checkedSmall
theorem b173 : Ban 25 5 v175 := checkedSmall
theorem b174 : Ban 25 5 v176 := checkedSmall
theorem b175 : Ban 25 5 v177 := checkedSmall
theorem b176 : Ban 25 5 v178 := checkedSmall
theorem b177 : Ban 25 5 v179 := checkedSmall
theorem b178 : Ban 25 5 v180 := checkedSmall
theorem b179 : Ban 25 5 v181 := checkedSmall
theorem b181 : Ban 25 5 v183 := checkedSmall
theorem b182 : Ban 25 5 v184 := checkedSmall
theorem b183 : Ban 25 5 v185 := checkedSmall
theorem b184 : Ban 25 5 v186 := checkedSmall
theorem b185 : Ban 25 5 v187 := checkedSmall
theorem b186 : Ban 25 5 v188 := checkedSmall
theorem b187 : Ban 25 5 v189 := checkedSmall
theorem b189 : Ban 25 5 v191 := checkedSmall
theorem b190 : Ban 25 5 v192 := checkedSmall
theorem b191 : Ban 25 5 v193 := checkedSmall
theorem b192 : Ban 25 5 v194 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b194 : Ban 25 6 v33 := viaBranch (ws := [v166,v167,v168,v169,v170,v171,v172,v173,v174,v31,v146,v175,v176,v177,v178,v179,v180,v181,v182,v183,v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v30]) (consBan b164 (consBan b165 (consBan b166 (consBan b167 (consBan b168 (consBan b169 (consBan b170 (consBan b171 (consBan b172 (consBan b27 (consBan b142 (consBan b173 (consBan b174 (consBan b175 (consBan b176 (consBan b177 (consBan b178 (consBan b179 (consBan b180 (consBan b181 (consBan b182 (consBan b183 (consBan b184 (consBan b185 (consBan b186 (consBan b187 (consBan b188 (consBan b189 (consBan b190 (consBan b191 (consBan b192 (consBan b193 (consBan b26 (nilBan 25 5)))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w4 : Wide 25 6 v33 := viaSub (ws := [v3,v33]) (consBan b44 (consBan b194 (nilBan 25 6))) (by decide) (by decide +kernel)
theorem b195 : Ban 46 7 v165 := smallByCut p63_61 w4
theorem b196 : Ban 46 7 v196 := smallByCut p63_42 w13
theorem b197 : Ban 46 7 v197 := smallByCut p63_21 w13
theorem b198 : Ban 46 7 v198 := smallByCut p63_42 w13
theorem b200 : Ban 46 7 v199 := smallByCut p63_61 w12
theorem b201 : Ban 46 7 v201 := smallByCut p63_21 w13
theorem b202 : Ban 46 7 v202 := smallByCut p63_21 w13
theorem b203 : Ban 46 7 v203 := smallByCut p63_21 w13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w5 : Wide 25 5 v43 := viaSub (ws := [v43]) (consBan b39 (nilBan 25 5)) (by decide) (by decide +kernel)
theorem b205 : Ban 46 7 v204 := smallByCut p63_55 w5
theorem b206 : Ban 46 7 v206 := smallByCut p63_21 w13
theorem b207 : Ban 46 7 v207 := smallByCut p63_21 w13
theorem b208 : Ban 26 5 v211 := checkedSmall
theorem b209 : Ban 26 5 v212 := checkedSmall
theorem b210 : Ban 26 5 v213 := checkedSmall
theorem b211 : Ban 26 5 v214 := checkedSmall
theorem b212 : Ban 26 5 v215 := checkedSmall
theorem b213 : Ban 26 5 v216 := checkedSmall
theorem b214 : Ban 26 5 v217 := checkedSmall
theorem b215 : Ban 26 5 v218 := checkedSmall
theorem b216 : Ban 26 5 v219 := checkedSmall
theorem b217 : Ban 26 5 v220 := checkedSmall
theorem b218 : Ban 26 5 v221 := checkedSmall
theorem b219 : Ban 26 5 v222 := checkedSmall
theorem b220 : Ban 26 5 v223 := checkedSmall
theorem b221 : Ban 26 5 v224 := checkedSmall
theorem b222 : Ban 26 5 v225 := checkedSmall
theorem b223 : Ban 26 5 v226 := checkedSmall
theorem b224 : Ban 26 5 v227 := checkedSmall
theorem b225 : Ban 26 5 v228 := checkedSmall
theorem b226 : Ban 26 5 v229 := checkedSmall
theorem b227 : Ban 26 5 v230 := checkedSmall
theorem b228 : Ban 26 5 v231 := checkedSmall
theorem b229 : Ban 26 5 v232 := checkedSmall
theorem b230 : Ban 26 5 v233 := checkedSmall
theorem b231 : Ban 26 5 v234 := checkedSmall
theorem b232 : Ban 26 5 v235 := checkedSmall
theorem b233 : Ban 26 5 v236 := checkedSmall
theorem b234 : Ban 26 5 v237 := checkedSmall
theorem b235 : Ban 26 5 v238 := checkedSmall
theorem b236 : Ban 26 5 v239 := checkedSmall
theorem b237 : Ban 26 5 v240 := checkedSmall
theorem b238 : Ban 26 5 v241 := checkedSmall
theorem b239 : Ban 26 5 v242 := checkedSmall
theorem b240 : Ban 26 5 v243 := checkedSmall
theorem b241 : Ban 26 5 v244 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b242 : Ban 26 6 v210 := viaBranch (ws := [v211,v212,v213,v214,v215,v216,v217,v218,v219,v70,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232,v233,v234,v235,v236,v237,v238,v239,v240,v241,v242,v243,v244]) (consBan b208 (consBan b209 (consBan b210 (consBan b211 (consBan b212 (consBan b213 (consBan b214 (consBan b215 (consBan b216 (consBan b64 (consBan b217 (consBan b218 (consBan b219 (consBan b220 (consBan b221 (consBan b222 (consBan b223 (consBan b224 (consBan b225 (consBan b226 (consBan b227 (consBan b228 (consBan b229 (consBan b230 (consBan b231 (consBan b232 (consBan b233 (consBan b234 (consBan b235 (consBan b236 (consBan b237 (consBan b238 (consBan b239 (consBan b240 (consBan b241 (nilBan 26 5)))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w6 : Wide 26 6 v210 := viaSub (ws := [v210]) (consBan b242 (nilBan 26 6)) (by decide) (by decide +kernel)
theorem b243 : Ban 46 7 v209 := smallByCut p63_62 w6
theorem b244 : Ban 46 7 v208 := viaPerm map63_5 map63_6 b243 (by decide +kernel) (by decide +kernel)
theorem b245 : Ban 46 7 v245 := smallByCut p63_61 w12
theorem b246 : Ban 46 7 v246 := smallByCut p63_61 w12
theorem b247 : Ban 46 7 v247 := smallByCut p63_21 w13
theorem b248 : Ban 46 7 v248 := smallByCut p63_42 w13
theorem b249 : Ban 46 7 v249 := smallByCut p63_21 w13
theorem b250 : Ban 46 7 v250 := viaPerm map63_7 map63_7 b243 (by decide +kernel) (by decide +kernel)
theorem b251 : Ban 46 7 v251 := smallByCut p63_61 w12
theorem b252 : Ban 46 7 v252 := smallByCut p63_61 w12
theorem b253 : Ban 46 7 v253 := smallByCut p63_21 w13
theorem b254 : Ban 46 7 v254 := smallByCut p63_42 w13
theorem b255 : Ban 46 7 v255 := smallByCut p63_21 w13
theorem b256 : Ban 46 6 v258 := smallByCut p63_42 w13
theorem b257 : Ban 46 6 v259 := smallByCut p63_42 w13
theorem b258 : Ban 46 6 v260 := smallByCut p63_42 w13
theorem b259 : Ban 46 6 v261 := smallByCut p63_42 w13
theorem b260 : Ban 46 6 v262 := smallByCut p63_42 w13
theorem b261 : Ban 46 6 v263 := smallByCut p63_42 w13
theorem b263 : Ban 46 6 v264 := smallByCut p63_42 w13
theorem b264 : Ban 46 6 v266 := smallByCut p63_42 w13
theorem b265 : Ban 46 6 v267 := smallByCut p63_42 w13
theorem b266 : Ban 46 6 v268 := smallByCut p63_42 w13
theorem b267 : Ban 46 6 v269 := smallByCut p63_47 w4
theorem b268 : Ban 46 6 v270 := smallByCut p63_62 w6
theorem b269 : Ban 46 6 v271 := smallByCut p63_42 w13
theorem b270 : Ban 46 6 v272 := checkedSmall
theorem b271 : Ban 46 6 v273 := smallByCut p63_42 w13
theorem b273 : Ban 46 6 v274 := smallByCut p63_59 w5
theorem b274 : Ban 46 6 v276 := smallByCut p63_42 w13
theorem b275 : Ban 46 6 v277 := smallByCut p63_42 w13
theorem b276 : Ban 46 6 v278 := smallByCut p63_42 w13
theorem b277 : Ban 46 6 v279 := smallByCut p63_42 w13
theorem b278 : Ban 46 6 v280 := smallByCut p63_42 w13
theorem b279 : Ban 46 6 v281 := smallByCut p63_42 w13
theorem b280 : Ban 46 6 v282 := smallByCut p63_42 w13
theorem b281 : Ban 46 6 v283 := smallByCut p63_42 w13
theorem b282 : Ban 46 6 v284 := smallByCut p63_21 w13
theorem b283 : Ban 46 6 v285 := smallByCut p63_42 w13
theorem b284 : Ban 46 6 v286 := smallByCut p63_21 w13
theorem b285 : Ban 46 6 v287 := smallByCut p63_42 w13
theorem b286 : Ban 46 6 v288 := smallByCut p63_21 w13
theorem b287 : Ban 46 6 v289 := smallByCut p63_21 w13
theorem b288 : Ban 46 6 v290 := smallByCut p63_42 w13
theorem b289 : Ban 46 6 v291 := smallByCut p63_21 w13
theorem b290 : Ban 46 6 v292 := smallByCut p63_42 w13
theorem b291 : Ban 46 6 v293 := smallByCut p63_42 w13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b292 : Ban 46 7 v257 := viaBranch (ws := [v258,v259,v260,v261,v262,v263,v264,v266,v267,v268,v269,v270,v271,v272,v273,v274,v276,v277,v278,v279,v280,v281,v282,v283,v284,v285,v286,v287,v288,v289,v290,v291,v292,v293]) (consBan b256 (consBan b257 (consBan b258 (consBan b259 (consBan b260 (consBan b261 (consBan b263 (consBan b264 (consBan b265 (consBan b266 (consBan b267 (consBan b268 (consBan b269 (consBan b270 (consBan b271 (consBan b273 (consBan b274 (consBan b275 (consBan b276 (consBan b277 (consBan b278 (consBan b279 (consBan b280 (consBan b281 (consBan b282 (consBan b283 (consBan b284 (consBan b285 (consBan b286 (consBan b287 (consBan b288 (consBan b289 (consBan b290 (consBan b291 (nilBan 46 6))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b293 : Ban 46 7 v256 := viaPerm map63_5 map63_6 b292 (by decide +kernel) (by decide +kernel)
theorem b294 : Ban 46 7 v294 := smallByCut p63_21 w13
theorem b295 : Ban 46 7 v295 := smallByCut p63_61 w12
theorem b296 : Ban 46 7 v296 := smallByCut p63_21 w13
theorem b297 : Ban 46 7 v297 := smallByCut p63_21 w13
theorem b299 : Ban 46 7 v298 := smallByCut p63_21 w13
theorem b300 : Ban 46 7 v300 := smallByCut p63_21 w13
theorem b301 : Ban 46 6 v303 := smallByCut p63_42 w13
theorem b302 : Ban 46 6 v304 := smallByCut p63_42 w13
theorem b303 : Ban 46 6 v305 := smallByCut p63_42 w13
theorem b304 : Ban 46 6 v306 := smallByCut p63_42 w13
theorem b305 : Ban 46 6 v307 := smallByCut p63_42 w13
theorem b306 : Ban 46 6 v308 := smallByCut p63_42 w13
theorem b307 : Ban 46 6 v309 := smallByCut p63_42 w13
theorem b308 : Ban 46 6 v310 := smallByCut p63_42 w13
theorem b309 : Ban 46 6 v311 := smallByCut p63_42 w13
theorem b310 : Ban 46 6 v312 := smallByCut p63_42 w13
theorem b311 : Ban 46 6 v313 := checkedSmall
theorem b312 : Ban 46 6 v314 := smallByCut p63_42 w13
theorem b313 : Ban 46 6 v315 := checkedSmall
theorem b314 : Ban 46 6 v316 := smallByCut p63_21 w13
theorem b315 : Ban 46 6 v317 := checkedSmall
theorem b316 : Ban 46 6 v318 := smallByCut p63_21 w13
theorem b317 : Ban 46 6 v319 := checkedSmall
theorem b318 : Ban 46 6 v320 := smallByCut p63_21 w13
theorem b319 : Ban 46 6 v321 := checkedSmall
theorem b320 : Ban 46 6 v322 := smallByCut p63_21 w13
theorem b321 : Ban 46 6 v323 := smallByCut p63_42 w13
theorem b323 : Ban 46 6 v324 := smallByCut p63_47 w5
theorem b324 : Ban 46 6 v326 := smallByCut p63_42 w13
theorem b325 : Ban 46 6 v327 := smallByCut p63_42 w13
theorem b326 : Ban 46 6 v328 := smallByCut p63_42 w13
theorem b327 : Ban 46 6 v329 := smallByCut p63_42 w13
theorem b328 : Ban 46 6 v330 := smallByCut p63_42 w13
theorem b329 : Ban 46 6 v331 := checkedSmall
theorem b330 : Ban 46 6 v332 := smallByCut p63_42 w13
theorem b331 : Ban 46 6 v333 := checkedSmall
theorem b332 : Ban 46 6 v334 := smallByCut p63_42 w13
theorem b333 : Ban 46 6 v335 := smallByCut p63_42 w13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b334 : Ban 46 7 v302 := viaBranch (ws := [v303,v304,v282,v305,v306,v307,v308,v309,v310,v311,v312,v313,v314,v315,v316,v317,v318,v319,v320,v321,v322,v323,v324,v326,v327,v328,v329,v330,v331,v332,v333,v334,v335]) (consBan b301 (consBan b302 (consBan b280 (consBan b303 (consBan b304 (consBan b305 (consBan b306 (consBan b307 (consBan b308 (consBan b309 (consBan b310 (consBan b311 (consBan b312 (consBan b313 (consBan b314 (consBan b315 (consBan b316 (consBan b317 (consBan b318 (consBan b319 (consBan b320 (consBan b321 (consBan b323 (consBan b324 (consBan b325 (consBan b326 (consBan b327 (consBan b328 (consBan b329 (consBan b330 (consBan b331 (consBan b332 (consBan b333 (nilBan 46 6)))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b335 : Ban 46 7 v301 := viaPerm map63_4 map63_4 b334 (by decide +kernel) (by decide +kernel)
theorem b336 : Ban 46 7 v336 := checkedSmall
theorem b356 : Ban 46 7 v337 := smallByCut p63_61 w7
theorem b357 : Ban 46 7 v356 := smallByCut p63_61 w7
theorem b358 : Ban 46 7 v357 := smallByCut p63_21 w13
theorem b359 : Ban 46 7 v358 := smallByCut p63_21 w13
theorem b361 : Ban 46 7 v359 := smallByCut p63_42 w13
theorem b362 : Ban 46 7 v361 := smallByCut p63_42 w13
theorem b363 : Ban 46 7 v362 := checkedSmall
theorem b364 : Ban 46 7 v363 := checkedSmall
theorem b396 : Ban 46 7 v365 := smallByCut p63_61 w12
theorem b397 : Ban 46 7 v364 := viaPerm map63_1 map63_1 b396 (by decide +kernel) (by decide +kernel)
theorem b398 : Ban 46 7 v397 := checkedSmall
theorem b399 : Ban 46 7 v398 := smallByCut p63_42 w13
theorem b400 : Ban 46 7 v399 := smallByCut p63_42 w13
theorem b401 : Ban 46 7 v400 := smallByCut p63_42 w13
theorem b402 : Ban 46 7 v401 := smallByCut p63_42 w13
theorem b403 : Ban 46 7 v402 := checkedSmall
theorem b404 : Ban 46 7 v403 := checkedSmall
theorem b405 : Ban 46 7 v404 := smallByCut p63_61 w12
theorem b406 : Ban 46 7 v405 := smallByCut p63_42 w13
theorem b407 : Ban 46 7 v406 := smallByCut p63_42 w13
theorem b409 : Ban 46 7 v407 := smallByCut p63_21 w13
theorem b411 : Ban 46 7 v409 := smallByCut p63_21 w13
theorem b412 : Ban 46 7 v411 := smallByCut p63_61 w3
theorem b413 : Ban 46 7 v412 := smallByCut p63_61 w3
theorem b414 : Ban 46 7 v413 := smallByCut p63_61 w4
theorem b415 : Ban 46 7 v414 := smallByCut p63_61 w4
theorem b417 : Ban 46 7 v415 := smallByCut p63_21 w13
theorem b418 : Ban 46 7 v417 := smallByCut p63_21 w13
theorem b419 : Ban 46 7 v418 := smallByCut p63_21 w13
theorem b420 : Ban 46 7 v419 := checkedSmall
theorem b421 : Ban 46 7 v420 := smallByCut p63_21 w13
theorem b422 : Ban 46 7 v421 := smallByCut p63_42 w13
theorem b423 : Ban 46 7 v422 := smallByCut p63_21 w13
theorem b424 : Ban 46 7 v423 := checkedSmall
theorem b425 : Ban 46 7 v424 := smallByCut p63_21 w13
theorem b426 : Ban 46 7 v425 := smallByCut p63_42 w13
theorem b428 : Ban 46 7 v426 := smallByCut p63_21 w13
theorem b429 : Ban 46 7 v428 := smallByCut p63_21 w13
theorem b431 : Ban 46 7 v429 := smallByCut p63_21 w13
theorem b433 : Ban 46 7 v431 := smallByCut p63_21 w13
theorem b435 : Ban 46 7 v433 := smallByCut p63_42 w13
theorem b436 : Ban 46 7 v435 := smallByCut p63_42 w13
theorem b437 : Ban 46 7 v436 := smallByCut p63_42 w13
theorem b438 : Ban 46 7 v437 := smallByCut p63_42 w13
theorem b439 : Ban 46 7 v438 := smallByCut p63_21 w13
theorem b440 : Ban 46 7 v439 := checkedSmall
theorem b441 : Ban 46 7 v440 := smallByCut p63_42 w13
theorem b442 : Ban 46 7 v441 := smallByCut p63_21 w13
theorem b443 : Ban 46 7 v442 := smallByCut p63_21 w13
theorem b444 : Ban 46 7 v443 := checkedSmall
theorem b445 : Ban 46 7 v444 := smallByCut p63_42 w13
theorem b446 : Ban 46 7 v445 := smallByCut p63_21 w13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b447 : Ban 46 8 v48 := viaBranch (ws := [v49,v51,v53,v56,v57,v58,v59,v60,v61,v63,v64,v117,v118,v119,v120,v121,v122,v123,v124,v125,v126,v127,v128,v129,v130,v164,v165,v196,v197,v198,v199,v201,v202,v203,v204,v206,v207,v208,v245,v246,v247,v248,v249,v250,v251,v252,v253,v254,v255,v256,v294,v295,v296,v297,v298,v300,v301,v336,v337,v356,v357,v358,v359,v361,v362,v363,v364,v397,v398,v399,v400,v401,v402,v403,v365,v404,v405,v406,v407,v409,v411,v412,v413,v414,v415,v417,v418,v419,v420,v421,v422,v423,v424,v425,v426,v428,v429,v431,v433,v435,v436,v437,v438,v439,v440,v441,v442,v443,v444,v445]) (consBan b48 (consBan b50 (consBan b53 (consBan b54 (consBan b55 (consBan b56 (consBan b57 (consBan b58 (consBan b60 (consBan b61 (consBan b114 (consBan b115 (consBan b116 (consBan b117 (consBan b118 (consBan b119 (consBan b120 (consBan b121 (consBan b122 (consBan b123 (consBan b124 (consBan b125 (consBan b126 (consBan b127 (consBan b162 (consBan b163 (consBan b195 (consBan b196 (consBan b197 (consBan b198 (consBan b200 (consBan b201 (consBan b202 (consBan b203 (consBan b205 (consBan b206 (consBan b207 (consBan b244 (consBan b245 (consBan b246 (consBan b247 (consBan b248 (consBan b249 (consBan b250 (consBan b251 (consBan b252 (consBan b253 (consBan b254 (consBan b255 (consBan b293 (consBan b294 (consBan b295 (consBan b296 (consBan b297 (consBan b299 (consBan b300 (consBan b335 (consBan b336 (consBan b356 (consBan b357 (consBan b358 (consBan b359 (consBan b361 (consBan b362 (consBan b363 (consBan b364 (consBan b397 (consBan b398 (consBan b399 (consBan b400 (consBan b401 (consBan b402 (consBan b403 (consBan b404 (consBan b396 (consBan b405 (consBan b406 (consBan b407 (consBan b409 (consBan b411 (consBan b412 (consBan b413 (consBan b414 (consBan b415 (consBan b417 (consBan b418 (consBan b419 (consBan b420 (consBan b421 (consBan b422 (consBan b423 (consBan b424 (consBan b425 (consBan b426 (consBan b428 (consBan b429 (consBan b431 (consBan b433 (consBan b435 (consBan b436 (consBan b437 (consBan b438 (consBan b439 (consBan b440 (consBan b441 (consBan b442 (consBan b443 (consBan b444 (consBan b445 (consBan b446 (nilBan 46 7))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b448 : Ban 46 7 v446 := smallByCut p63_21 w13
theorem b449 : Ban 46 7 v1 := smallByCut p63_21 w13
theorem b450 : Ban 46 7 v447 := smallByCut p63_21 w13
theorem b451 : Ban 46 7 v48 := smallByCut p63_61 w12
theorem b452 : Ban 46 7 v448 := smallByCut p63_21 w13
theorem b453 : Ban 46 7 v449 := smallByCut p63_21 w13
theorem b454 : Ban 46 6 v452 := smallByCut p63_21 w13
theorem b455 : Ban 46 6 v453 := smallByCut p63_21 w13
theorem b456 : Ban 46 6 v454 := smallByCut p63_21 w13
theorem b457 : Ban 46 6 v455 := smallByCut p63_21 w13
theorem b458 : Ban 46 6 v456 := smallByCut p63_21 w13
theorem b459 : Ban 46 6 v457 := smallByCut p63_21 w13
theorem b460 : Ban 46 6 v458 := smallByCut p63_21 w13
theorem b461 : Ban 46 6 v459 := smallByCut p63_21 w13
theorem b462 : Ban 46 6 v460 := smallByCut p63_42 w13
theorem b463 : Ban 46 6 v461 := smallByCut p63_42 w13
theorem b464 : Ban 46 6 v462 := smallByCut p63_42 w13
theorem b465 : Ban 46 6 v463 := smallByCut p63_42 w13
theorem b466 : Ban 46 6 v464 := smallByCut p63_42 w13
theorem b467 : Ban 46 6 v465 := checkedSmall
theorem b468 : Ban 46 6 v466 := smallByCut p63_21 w13
theorem b469 : Ban 46 6 v467 := checkedSmall
theorem b470 : Ban 46 6 v468 := smallByCut p63_21 w13
theorem solidb147 : Wide 25 5 v151 := solid b147
theorem b471 : Ban 46 6 v469 := smallByCut p63_59 solidb147
theorem b472 : Ban 46 6 v470 := smallByCut p63_21 w13
theorem b473 : Ban 46 6 v471 := smallByCut p63_21 w13
theorem b474 : Ban 46 6 v472 := smallByCut p63_21 w13
theorem b475 : Ban 46 6 v473 := smallByCut p63_21 w13
theorem b476 : Ban 46 6 v474 := smallByCut p63_21 w13
theorem b477 : Ban 46 6 v475 := smallByCut p63_21 w13
theorem b478 : Ban 46 6 v476 := smallByCut p63_21 w13
theorem b479 : Ban 46 6 v477 := smallByCut p63_21 w13
theorem b480 : Ban 46 6 v478 := smallByCut p63_21 w13
theorem b481 : Ban 46 6 v479 := smallByCut p63_21 w13
theorem b482 : Ban 46 6 v480 := smallByCut p63_21 w13
theorem b483 : Ban 46 6 v481 := smallByCut p63_21 w13
theorem b484 : Ban 46 6 v482 := smallByCut p63_21 w13
theorem b485 : Ban 46 6 v483 := smallByCut p63_21 w13
theorem b486 : Ban 46 6 v484 := smallByCut p63_21 w13
theorem b487 : Ban 46 6 v485 := smallByCut p63_21 w13
theorem b488 : Ban 46 6 v486 := smallByCut p63_21 w13
theorem b489 : Ban 46 6 v487 := smallByCut p63_21 w13
theorem b490 : Ban 46 6 v488 := smallByCut p63_21 w13
theorem b491 : Ban 46 6 v489 := smallByCut p63_21 w13
theorem b492 : Ban 46 6 v490 := smallByCut p63_21 w13
theorem b493 : Ban 46 6 v491 := smallByCut p63_21 w13
theorem b494 : Ban 46 6 v492 := smallByCut p63_21 w13
theorem b495 : Ban 46 6 v493 := smallByCut p63_21 w13
theorem b496 : Ban 46 6 v494 := smallByCut p63_21 w13
theorem b497 : Ban 46 6 v495 := smallByCut p63_21 w13
theorem b498 : Ban 46 6 v496 := smallByCut p63_21 w13
theorem b499 : Ban 46 6 v497 := smallByCut p63_21 w13
theorem b500 : Ban 46 6 v498 := smallByCut p63_21 w13
theorem b501 : Ban 46 6 v499 := smallByCut p63_21 w13
theorem b502 : Ban 46 6 v500 := smallByCut p63_21 w13
theorem b503 : Ban 46 6 v501 := smallByCut p63_21 w13
theorem b504 : Ban 46 6 v502 := smallByCut p63_42 w13
theorem b505 : Ban 46 6 v503 := smallByCut p63_59 w5
theorem b506 : Ban 46 6 v504 := smallByCut p63_42 w13
theorem b507 : Ban 46 6 v505 := smallByCut p63_47 w7
theorem b508 : Ban 46 6 v506 := smallByCut p63_21 w13
theorem b509 : Ban 46 6 v507 := smallByCut p63_21 w13
theorem b510 : Ban 46 6 v508 := smallByCut p63_21 w13
theorem b511 : Ban 46 6 v509 := smallByCut p63_21 w13
theorem b512 : Ban 46 6 v510 := smallByCut p63_21 w13
theorem b513 : Ban 46 6 v511 := smallByCut p63_21 w13
theorem b514 : Ban 46 6 v512 := smallByCut p63_21 w13
theorem b515 : Ban 46 6 v513 := smallByCut p63_21 w13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b516 : Ban 46 7 v451 := viaBranch (ws := [v452,v453,v454,v455,v456,v457,v458,v459,v460,v461,v462,v463,v464,v465,v466,v467,v468,v469,v470,v471,v472,v473,v474,v475,v476,v477,v478,v479,v480,v481,v482,v483,v484,v485,v486,v487,v488,v489,v490,v491,v492,v493,v494,v495,v496,v497,v498,v499,v500,v501,v502,v503,v504,v505,v506,v507,v508,v509,v510,v511,v512,v513]) (consBan b454 (consBan b455 (consBan b456 (consBan b457 (consBan b458 (consBan b459 (consBan b460 (consBan b461 (consBan b462 (consBan b463 (consBan b464 (consBan b465 (consBan b466 (consBan b467 (consBan b468 (consBan b469 (consBan b470 (consBan b471 (consBan b472 (consBan b473 (consBan b474 (consBan b475 (consBan b476 (consBan b477 (consBan b478 (consBan b479 (consBan b480 (consBan b481 (consBan b482 (consBan b483 (consBan b484 (consBan b485 (consBan b486 (consBan b487 (consBan b488 (consBan b489 (consBan b490 (consBan b491 (consBan b492 (consBan b493 (consBan b494 (consBan b495 (consBan b496 (consBan b497 (consBan b498 (consBan b499 (consBan b500 (consBan b501 (consBan b502 (consBan b503 (consBan b504 (consBan b505 (consBan b506 (consBan b507 (consBan b508 (consBan b509 (consBan b510 (consBan b511 (consBan b512 (consBan b513 (consBan b514 (consBan b515 (nilBan 46 6))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b517 : Ban 46 7 v450 := viaPerm map63_4 map63_4 b516 (by decide +kernel) (by decide +kernel)
theorem b518 : Ban 46 7 v514 := smallByCut p63_42 w13
theorem b520 : Ban 46 7 v515 := smallByCut p63_55 w7
theorem b521 : Ban 46 7 v517 := smallByCut p63_42 w13
theorem b522 : Ban 46 7 v518 := smallByCut p63_42 w13
theorem b523 : Ban 46 7 v519 := smallByCut p63_42 w13
theorem b525 : Ban 46 7 v520 := smallByCut p63_55 w12
theorem b526 : Ban 46 7 v522 := smallByCut p63_42 w13
theorem b528 : Ban 46 7 v523 := smallByCut p63_21 w13
theorem b529 : Ban 46 7 v525 := smallByCut p63_21 w13
theorem b531 : Ban 46 7 v526 := smallByCut p63_42 w13
theorem b534 : Ban 46 7 v528 := smallByCut p63_42 w13
theorem b536 : Ban 46 7 v530 := smallByCut p63_42 w13
theorem b537 : Ban 46 7 v532 := smallByCut p63_42 w13
theorem b538 : Ban 46 7 v533 := smallByCut p63_42 w13
theorem b539 : Ban 46 7 v534 := smallByCut p63_42 w13
theorem b541 : Ban 46 7 v535 := smallByCut p63_42 w13
theorem b542 : Ban 46 7 v537 := smallByCut p63_42 w13
theorem b543 : Ban 46 7 v538 := smallByCut p63_42 w13
theorem b544 : Ban 46 7 v539 := smallByCut p63_42 w13
theorem b545 : Ban 46 7 v540 := smallByCut p63_42 w13
theorem b546 : Ban 46 7 v541 := smallByCut p63_42 w13
theorem b547 : Ban 46 7 v542 := smallByCut p63_42 w13
theorem b548 : Ban 46 7 v543 := smallByCut p63_42 w13
theorem b549 : Ban 46 7 v544 := smallByCut p63_42 w13
theorem b550 : Ban 46 7 v545 := smallByCut p63_42 w13
theorem b552 : Ban 46 7 v546 := smallByCut p63_21 w13
theorem b554 : Ban 46 7 v548 := smallByCut p63_21 w13
theorem b556 : Ban 46 7 v550 := smallByCut p63_61 w3
theorem b557 : Ban 46 7 v552 := smallByCut p63_42 w13
theorem b558 : Ban 46 7 v553 := smallByCut p63_42 w13
theorem b559 : Ban 46 7 v554 := smallByCut p63_42 w13
theorem b561 : Ban 46 7 v555 := smallByCut p63_21 w13
theorem b562 : Ban 46 7 v557 := smallByCut p63_21 w13
theorem b563 : Ban 46 7 v558 := smallByCut p63_61 w12
theorem b564 : Ban 46 7 v559 := smallByCut p63_42 w13
theorem b565 : Ban 46 7 v560 := smallByCut p63_21 w13
theorem b566 : Ban 46 7 v561 := smallByCut p63_21 w13
theorem b567 : Ban 46 7 v562 := smallByCut p63_21 w13
theorem b568 : Ban 46 7 v563 := smallByCut p63_55 w7
theorem b569 : Ban 46 7 v564 := smallByCut p63_42 w13
theorem b570 : Ban 46 7 v565 := smallByCut p63_42 w13
theorem b571 : Ban 46 7 v566 := smallByCut p63_42 w13
theorem b572 : Ban 46 7 v567 := smallByCut p63_21 w13
theorem b574 : Ban 46 7 v568 := smallByCut p63_42 w13
theorem b575 : Ban 46 7 v570 := smallByCut p63_42 w13
theorem b576 : Ban 46 7 v571 := smallByCut p63_42 w13
theorem b577 : Ban 46 7 v572 := smallByCut p63_42 w13
theorem b573 : Ban 46 7 v569 := smallByCut p63_42 w13
theorem b578 : Ban 46 7 v573 := smallByCut p63_42 w13
theorem b579 : Ban 46 7 v574 := smallByCut p63_42 w13
theorem b580 : Ban 46 7 v575 := smallByCut p63_42 w13
theorem b581 : Ban 46 7 v576 := smallByCut p63_21 w13
theorem b582 : Ban 46 7 v577 := smallByCut p63_61 w3
theorem b583 : Ban 46 7 v578 := smallByCut p63_42 w13
theorem b584 : Ban 46 7 v579 := smallByCut p63_42 w13
theorem b585 : Ban 46 7 v580 := smallByCut p63_42 w13
theorem b586 : Ban 46 7 v581 := smallByCut p63_21 w13
theorem b587 : Ban 46 7 v582 := smallByCut p63_21 w13
theorem b588 : Ban 46 7 v583 := smallByCut p63_21 w13
theorem b589 : Ban 46 7 v584 := smallByCut p63_21 w13
theorem b590 : Ban 46 7 v585 := smallByCut p63_21 w13
theorem b591 : Ban 46 7 v586 := smallByCut p63_21 w13
theorem b592 : Ban 46 7 v587 := smallByCut p63_42 w13
theorem b593 : Ban 46 7 v588 := smallByCut p63_21 w13
theorem b594 : Ban 46 7 v589 := smallByCut p63_42 w13
theorem b595 : Ban 46 7 v590 := smallByCut p63_21 w13
theorem b596 : Ban 46 7 v591 := smallByCut p63_42 w13
theorem b597 : Ban 46 7 v592 := smallByCut p63_21 w13
theorem b598 : Ban 46 7 v593 := smallByCut p63_42 w13
theorem b600 : Ban 46 7 v594 := smallByCut p63_21 w13
theorem b601 : Ban 46 7 v596 := smallByCut p63_21 w13
theorem b602 : Ban 46 7 v597 := smallByCut p63_21 w13
theorem b603 : Ban 46 7 v598 := smallByCut p63_21 w13
theorem b604 : Ban 46 7 v599 := smallByCut p63_21 w13
theorem b605 : Ban 46 7 v600 := smallByCut p63_42 w13
theorem b606 : Ban 46 7 v601 := smallByCut p63_21 w13
theorem b607 : Ban 46 7 v602 := smallByCut p63_42 w13
theorem b608 : Ban 46 7 v603 := smallByCut p63_21 w13
theorem b609 : Ban 46 7 v604 := smallByCut p63_42 w13
theorem b610 : Ban 46 7 v605 := smallByCut p63_21 w13
theorem b611 : Ban 46 7 v606 := smallByCut p63_42 w13
theorem b613 : Ban 46 7 v607 := smallByCut p63_21 w13
theorem b614 : Ban 46 7 v609 := smallByCut p63_21 w13
theorem b615 : Ban 46 7 v610 := smallByCut p63_21 w13
theorem b616 : Ban 46 7 v611 := smallByCut p63_21 w13
theorem b618 : Ban 46 7 v612 := smallByCut p63_42 w13
theorem b619 : Ban 46 7 v614 := smallByCut p63_42 w13
theorem b620 : Ban 46 7 v615 := smallByCut p63_42 w13
theorem b621 : Ban 46 7 v616 := smallByCut p63_42 w13
theorem b622 : Ban 46 7 v617 := smallByCut p63_21 w13
theorem b623 : Ban 46 7 v618 := smallByCut p63_42 w13
theorem b624 : Ban 46 7 v619 := smallByCut p63_42 w13
theorem b626 : Ban 46 7 v620 := smallByCut p63_21 w13
theorem b627 : Ban 46 7 v622 := smallByCut p63_21 w13
theorem b628 : Ban 46 7 v623 := smallByCut p63_42 w13
theorem b629 : Ban 46 7 v624 := smallByCut p63_42 w13
theorem b625 : Ban 46 7 v621 := smallByCut p63_21 w13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b630 : Ban 46 8 v198 := viaBranch (ws := [v446,v1,v447,v57,v48,v58,v448,v449,v450,v514,v515,v517,v518,v519,v520,v522,v523,v525,v526,v528,v530,v532,v533,v534,v535,v537,v538,v539,v540,v541,v542,v543,v544,v545,v546,v548,v550,v552,v553,v554,v555,v557,v558,v559,v560,v561,v562,v563,v564,v565,v566,v567,v568,v570,v571,v572,v569,v573,v574,v575,v576,v577,v578,v579,v580,v581,v582,v583,v584,v585,v586,v587,v588,v589,v590,v591,v592,v593,v594,v596,v597,v598,v599,v600,v601,v602,v603,v604,v605,v606,v607,v609,v610,v611,v612,v614,v615,v616,v617,v618,v619,v620,v622,v623,v624,v621]) (consBan b448 (consBan b449 (consBan b450 (consBan b55 (consBan b451 (consBan b56 (consBan b452 (consBan b453 (consBan b517 (consBan b518 (consBan b520 (consBan b521 (consBan b522 (consBan b523 (consBan b525 (consBan b526 (consBan b528 (consBan b529 (consBan b531 (consBan b534 (consBan b536 (consBan b537 (consBan b538 (consBan b539 (consBan b541 (consBan b542 (consBan b543 (consBan b544 (consBan b545 (consBan b546 (consBan b547 (consBan b548 (consBan b549 (consBan b550 (consBan b552 (consBan b554 (consBan b556 (consBan b557 (consBan b558 (consBan b559 (consBan b561 (consBan b562 (consBan b563 (consBan b564 (consBan b565 (consBan b566 (consBan b567 (consBan b568 (consBan b569 (consBan b570 (consBan b571 (consBan b572 (consBan b574 (consBan b575 (consBan b576 (consBan b577 (consBan b573 (consBan b578 (consBan b579 (consBan b580 (consBan b581 (consBan b582 (consBan b583 (consBan b584 (consBan b585 (consBan b586 (consBan b587 (consBan b588 (consBan b589 (consBan b590 (consBan b591 (consBan b592 (consBan b593 (consBan b594 (consBan b595 (consBan b596 (consBan b597 (consBan b598 (consBan b600 (consBan b601 (consBan b602 (consBan b603 (consBan b604 (consBan b605 (consBan b606 (consBan b607 (consBan b608 (consBan b609 (consBan b610 (consBan b611 (consBan b613 (consBan b614 (consBan b615 (consBan b616 (consBan b618 (consBan b619 (consBan b620 (consBan b621 (consBan b622 (consBan b623 (consBan b624 (consBan b626 (consBan b627 (consBan b628 (consBan b629 (consBan b625 (nilBan 46 7))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b632 : Ban 46 8 v61 := smallByCut p63_61 w12
theorem b633 : Ban 46 8 v625 := smallByCut p63_55 w12
theorem b634 : Ban 46 8 v626 := viaPerm map63_2 map63_2 b447 (by decide +kernel) (by decide +kernel)
theorem b635 : Ban 46 8 v627 := viaPerm map63_2 map63_2 b630 (by decide +kernel) (by decide +kernel)
theorem b636 : Ban 46 8 v628 := smallByCut p63_55 w12
theorem b638 : Ban 46 8 v629 := smallByCut p63_59 w12
theorem b639 : Ban 46 7 v632 := smallByCut p63_42 w13
theorem b640 : Ban 46 7 v633 := smallByCut p63_42 w13
theorem b641 : Ban 46 7 v634 := smallByCut p63_42 w13
theorem b642 : Ban 46 7 v635 := smallByCut p63_42 w13
theorem b643 : Ban 46 7 v636 := smallByCut p63_42 w13
theorem b644 : Ban 46 7 v637 := smallByCut p63_42 w13
theorem b646 : Ban 46 7 v638 := smallByCut p63_59 w12
theorem b648 : Ban 46 7 v640 := smallByCut p63_42 w13
theorem b650 : Ban 46 7 v642 := smallByCut p63_42 w13
theorem b652 : Ban 46 7 v644 := smallByCut p63_42 w13
theorem b654 : Ban 46 7 v646 := smallByCut p63_42 w13
theorem b655 : Ban 46 7 v648 := smallByCut p63_42 w13
theorem b657 : Ban 46 7 v649 := smallByCut p63_42 w13
theorem b658 : Ban 46 7 v651 := smallByCut p63_42 w13
theorem b660 : Ban 46 7 v652 := smallByCut p63_42 w13
theorem b661 : Ban 46 7 v654 := smallByCut p63_42 w13
theorem b663 : Ban 46 7 v655 := smallByCut p63_42 w13
theorem b664 : Ban 46 7 v657 := smallByCut p63_42 w13
theorem b665 : Ban 46 7 v658 := smallByCut p63_42 w13
theorem b666 : Ban 46 7 v659 := smallByCut p63_42 w13
theorem b667 : Ban 46 7 v660 := smallByCut p63_42 w13
theorem b668 : Ban 46 7 v661 := smallByCut p63_42 w13
theorem b669 : Ban 46 7 v662 := smallByCut p63_42 w13
theorem b670 : Ban 46 7 v663 := smallByCut p63_42 w13
theorem b671 : Ban 46 7 v664 := smallByCut p63_42 w13
theorem b365 : Ban 25 5 v367 := checkedSmall
theorem b366 : Ban 25 5 v368 := checkedSmall
theorem b367 : Ban 25 5 v369 := checkedSmall
theorem b368 : Ban 25 5 v370 := checkedSmall
theorem b369 : Ban 25 5 v371 := checkedSmall
theorem b370 : Ban 25 5 v372 := checkedSmall
theorem b371 : Ban 25 5 v373 := checkedSmall
theorem b372 : Ban 25 5 v374 := checkedSmall
theorem b373 : Ban 25 5 v375 := checkedSmall
theorem b374 : Ban 25 5 v376 := checkedSmall
theorem b375 : Ban 25 5 v377 := checkedSmall
theorem b376 : Ban 25 5 v378 := checkedSmall
theorem b377 : Ban 25 5 v379 := checkedSmall
theorem b378 : Ban 25 5 v380 := checkedSmall
theorem b379 : Ban 25 5 v381 := checkedSmall
theorem b380 : Ban 25 5 v382 := checkedSmall
theorem b381 : Ban 25 5 v383 := checkedSmall
theorem b382 : Ban 25 5 v384 := checkedSmall
theorem b383 : Ban 25 5 v385 := checkedSmall
theorem b384 : Ban 25 5 v386 := checkedSmall
theorem b385 : Ban 25 5 v387 := checkedSmall
theorem b386 : Ban 25 5 v388 := checkedSmall
theorem b387 : Ban 25 5 v389 := checkedSmall
theorem b388 : Ban 25 5 v390 := checkedSmall
theorem b389 : Ban 25 5 v391 := checkedSmall
theorem b392 : Ban 25 5 v394 := checkedSmall
theorem b393 : Ban 25 5 v395 := checkedSmall
theorem b394 : Ban 25 5 v396 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b395 : Ban 25 6 v366 := viaBranch (ws := [v367,v368,v369,v370,v371,v372,v373,v374,v375,v376,v377,v378,v379,v380,v381,v382,v383,v384,v385,v386,v387,v388,v389,v390,v391,v37,v392,v393,v394,v34,v350,v41,v395,v38,v396]) (consBan b365 (consBan b366 (consBan b367 (consBan b368 (consBan b369 (consBan b370 (consBan b371 (consBan b372 (consBan b373 (consBan b374 (consBan b375 (consBan b376 (consBan b377 (consBan b378 (consBan b379 (consBan b380 (consBan b381 (consBan b382 (consBan b383 (consBan b384 (consBan b385 (consBan b386 (consBan b387 (consBan b388 (consBan b389 (consBan b33 (consBan b390 (consBan b391 (consBan b392 (consBan b30 (consBan b349 (consBan b37 (consBan b393 (consBan b34 (consBan b394 (nilBan 25 5)))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w8 : Wide 25 6 v366 := viaSub (ws := [v3,v366]) (consBan b44 (consBan b395 (nilBan 25 6))) (by decide) (by decide +kernel)
theorem b672 : Ban 25 5 v3 := bySubset w8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w10 : Wide 25 5 v17 := viaSub (ws := [v3,v17]) (consBan b672 (consBan b13 (nilBan 25 5))) (by decide) (by decide +kernel)
theorem b673 : Ban 46 7 v665 := smallByCut p63_55 w10
theorem b674 : Ban 46 7 v666 := checkedSmall
theorem b675 : Ban 46 7 v667 := smallByCut p63_61 w10
theorem b676 : Ban 46 7 v668 := smallByCut p63_55 w10
theorem b677 : Ban 46 7 v669 := smallByCut p63_42 w13
theorem b678 : Ban 46 7 v670 := smallByCut p63_42 w13
theorem b679 : Ban 46 7 v671 := smallByCut p63_42 w13
theorem b680 : Ban 46 7 v672 := smallByCut p63_42 w13
theorem b681 : Ban 46 7 v673 := smallByCut p63_21 w13
theorem b682 : Ban 46 7 v674 := smallByCut p63_42 w13
theorem b683 : Ban 46 7 v675 := smallByCut p63_42 w13
theorem b684 : Ban 46 7 v676 := smallByCut p63_21 w13
theorem b685 : Ban 46 7 v677 := smallByCut p63_42 w13
theorem b686 : Ban 46 7 v678 := smallByCut p63_42 w13
theorem b687 : Ban 46 7 v679 := smallByCut p63_42 w13
theorem b688 : Ban 46 7 v680 := smallByCut p63_42 w13
theorem b689 : Ban 46 7 v681 := smallByCut p63_42 w13
theorem b690 : Ban 46 7 v682 := smallByCut p63_42 w13
theorem b691 : Ban 46 7 v683 := smallByCut p63_42 w13
theorem b693 : Ban 46 7 v684 := smallByCut p63_61 w10
theorem b694 : Ban 46 6 v687 := smallByCut p63_59 w10
theorem b695 : Ban 46 6 v688 := smallByCut p63_61 w10
theorem b696 : Ban 46 6 v689 := smallByCut p63_55 w10
theorem b755 : Ban 25 5 v750 := checkedSmall
theorem b756 : Ban 25 5 v751 := checkedSmall
theorem b757 : Ban 25 5 v752 := checkedSmall
theorem b758 : Ban 25 5 v753 := checkedSmall
theorem b759 : Ban 25 5 v754 := checkedSmall
theorem b760 : Ban 25 5 v755 := checkedSmall
theorem b761 : Ban 25 5 v756 := checkedSmall
theorem b762 : Ban 25 5 v757 := checkedSmall
theorem b763 : Ban 25 5 v758 := checkedSmall
theorem b764 : Ban 25 5 v759 := checkedSmall
theorem b765 : Ban 25 5 v760 := checkedSmall
theorem b766 : Ban 25 5 v761 := checkedSmall
theorem b767 : Ban 25 5 v762 := checkedSmall
theorem b768 : Ban 25 5 v763 := checkedSmall
theorem b769 : Ban 25 5 v764 := checkedSmall
theorem b770 : Ban 25 5 v765 := checkedSmall
theorem b771 : Ban 25 5 v766 := checkedSmall
theorem b772 : Ban 25 5 v767 := checkedSmall
theorem b773 : Ban 25 5 v768 := checkedSmall
theorem b774 : Ban 25 5 v769 := checkedSmall
theorem b775 : Ban 25 5 v770 := checkedSmall
theorem b776 : Ban 25 5 v771 := checkedSmall
theorem b777 : Ban 25 5 v772 := checkedSmall
theorem b778 : Ban 25 5 v773 := checkedSmall
theorem b779 : Ban 25 5 v774 := checkedSmall
theorem b780 : Ban 25 5 v775 := checkedSmall
theorem b781 : Ban 25 5 v776 := checkedSmall
theorem b782 : Ban 25 5 v777 := checkedSmall
theorem b783 : Ban 25 5 v778 := checkedSmall
theorem b784 : Ban 25 5 v779 := checkedSmall
theorem b785 : Ban 25 5 v780 := checkedSmall
theorem b786 : Ban 25 5 v781 := checkedSmall
theorem b787 : Ban 25 5 v782 := checkedSmall
theorem b788 : Ban 25 5 v783 := checkedSmall
theorem b789 : Ban 25 5 v784 := checkedSmall
theorem b790 : Ban 25 5 v785 := checkedSmall
theorem b791 : Ban 25 5 v786 := checkedSmall
theorem b792 : Ban 25 5 v787 := checkedSmall
theorem b793 : Ban 25 5 v788 := checkedSmall
theorem b794 : Ban 25 5 v789 := checkedSmall
theorem b795 : Ban 25 5 v790 := checkedSmall
theorem b796 : Ban 25 5 v791 := checkedSmall
theorem b797 : Ban 25 5 v792 := checkedSmall
theorem b798 : Ban 25 5 v793 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b799 : Ban 25 6 v749 := viaBranch (ws := [v750,v751,v752,v753,v754,v755,v756,v757,v758,v759,v760,v761,v762,v763,v764,v765,v766,v767,v768,v769,v770,v771,v772,v773,v774,v775,v776,v777,v778,v779,v780,v781,v782,v783,v784,v785,v786,v787,v788,v789,v790,v791,v792,v793]) (consBan b755 (consBan b756 (consBan b757 (consBan b758 (consBan b759 (consBan b760 (consBan b761 (consBan b762 (consBan b763 (consBan b764 (consBan b765 (consBan b766 (consBan b767 (consBan b768 (consBan b769 (consBan b770 (consBan b771 (consBan b772 (consBan b773 (consBan b774 (consBan b775 (consBan b776 (consBan b777 (consBan b778 (consBan b779 (consBan b780 (consBan b781 (consBan b782 (consBan b783 (consBan b784 (consBan b785 (consBan b786 (consBan b787 (consBan b788 (consBan b789 (consBan b790 (consBan b791 (consBan b792 (consBan b793 (consBan b794 (consBan b795 (consBan b796 (consBan b797 (consBan b798 (nilBan 25 5))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w11 : Wide 25 6 v749 := viaSub (ws := [v749]) (consBan b799 (nilBan 25 6)) (by decide) (by decide +kernel)
theorem b697 : Ban 46 6 v690 := smallByCut p63_59 w11
theorem b698 : Ban 46 6 v691 := smallByCut p63_47 w10
theorem b699 : Ban 46 6 v692 := smallByCut p63_61 w11
theorem b700 : Ban 46 6 v693 := smallByCut p63_21 w13
theorem b701 : Ban 46 6 v694 := checkedSmall
theorem b702 : Ban 46 6 v695 := smallByCut p63_42 w13
theorem b703 : Ban 46 6 v696 := smallByCut p63_21 w13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b704 : Ban 46 7 v686 := viaBranch (ws := [v687,v688,v689,v690,v691,v692,v693,v694,v695,v696]) (consBan b694 (consBan b695 (consBan b696 (consBan b697 (consBan b698 (consBan b699 (consBan b700 (consBan b701 (consBan b702 (consBan b703 (nilBan 46 6))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b705 : Ban 46 7 v697 := smallByCut p63_61 w10
theorem b706 : Ban 46 7 v698 := checkedSmall
theorem b707 : Ban 46 7 v699 := smallByCut p63_42 w13
theorem b708 : Ban 46 7 v700 := smallByCut p63_42 w13
theorem b709 : Ban 46 7 v701 := smallByCut p63_42 w13
theorem b710 : Ban 46 7 v702 := smallByCut p63_42 w13
theorem b711 : Ban 46 7 v703 := smallByCut p63_21 w13
theorem b712 : Ban 46 7 v704 := smallByCut p63_42 w13
theorem b713 : Ban 46 7 v705 := checkedSmall
theorem b714 : Ban 46 7 v706 := smallByCut p63_42 w13
theorem b715 : Ban 46 7 v707 := smallByCut p63_21 w13
theorem b716 : Ban 46 7 v708 := smallByCut p63_42 w13
theorem b717 : Ban 46 7 v709 := smallByCut p63_42 w13
theorem b718 : Ban 46 7 v710 := smallByCut p63_42 w13
theorem b719 : Ban 46 7 v711 := smallByCut p63_42 w13
theorem b720 : Ban 46 7 v712 := smallByCut p63_42 w13
theorem b721 : Ban 46 7 v713 := smallByCut p63_42 w13
theorem b722 : Ban 46 7 v714 := smallByCut p63_42 w13
theorem b723 : Ban 46 7 v715 := smallByCut p63_55 w10
theorem b724 : Ban 46 7 v716 := viaPerm map63_2 map63_2 b704 (by decide +kernel) (by decide +kernel)
theorem b725 : Ban 46 7 v717 := smallByCut p63_55 w10
theorem b726 : Ban 46 7 v718 := smallByCut p63_42 w13
theorem b728 : Ban 46 7 v719 := smallByCut p63_42 w13
theorem b730 : Ban 46 7 v721 := smallByCut p63_42 w13
theorem b732 : Ban 46 7 v723 := smallByCut p63_42 w13
theorem b733 : Ban 46 7 v725 := smallByCut p63_42 w13
theorem b735 : Ban 46 7 v726 := smallByCut p63_42 w13
theorem b736 : Ban 46 7 v728 := smallByCut p63_42 w13
theorem b738 : Ban 46 7 v729 := smallByCut p63_42 w13
theorem b739 : Ban 46 7 v731 := smallByCut p63_42 w13
theorem b740 : Ban 46 7 v732 := viaPerm map63_1 map63_1 b292 (by decide +kernel) (by decide +kernel)
theorem b741 : Ban 46 7 v733 := smallByCut p63_42 w13
theorem b742 : Ban 46 7 v734 := smallByCut p63_42 w13
theorem b743 : Ban 46 7 v735 := smallByCut p63_42 w13
theorem b744 : Ban 46 7 v736 := smallByCut p63_42 w13
theorem b746 : Ban 46 7 v737 := smallByCut p63_47 w12
theorem b748 : Ban 46 7 v739 := smallByCut p63_42 w13
theorem b750 : Ban 46 7 v741 := smallByCut p63_42 w13
theorem b752 : Ban 46 7 v743 := smallByCut p63_42 w13
theorem b753 : Ban 46 7 v745 := smallByCut p63_42 w13
theorem b754 : Ban 46 7 v746 := smallByCut p63_42 w13
theorem b801 : Ban 46 7 v747 := smallByCut p63_55 w11
theorem b803 : Ban 46 7 v794 := smallByCut p63_42 w13
theorem b804 : Ban 46 7 v796 := smallByCut p63_42 w13
theorem b805 : Ban 46 7 v797 := smallByCut p63_42 w13
theorem b807 : Ban 46 7 v798 := smallByCut p63_42 w13
theorem b808 : Ban 46 7 v800 := smallByCut p63_42 w13
theorem b809 : Ban 46 7 v801 := smallByCut p63_21 w13
theorem b810 : Ban 46 7 v802 := smallByCut p63_42 w13
theorem b811 : Ban 46 7 v803 := smallByCut p63_59 w3
theorem b812 : Ban 46 7 v804 := smallByCut p63_42 w13
theorem b813 : Ban 46 7 v805 := smallByCut p63_42 w13
theorem b814 : Ban 46 7 v806 := smallByCut p63_42 w13
theorem b815 : Ban 46 7 v807 := smallByCut p63_21 w13
theorem b816 : Ban 46 7 v808 := smallByCut p63_42 w13
theorem b817 : Ban 46 7 v809 := smallByCut p63_42 w13
theorem b818 : Ban 46 7 v810 := smallByCut p63_42 w13
theorem b820 : Ban 46 7 v811 := smallByCut p63_42 w13
theorem b821 : Ban 46 7 v813 := smallByCut p63_42 w13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b822 : Ban 46 8 v631 := viaBranch (ws := [v632,v122,v570,v633,v634,v635,v636,v637,v638,v640,v642,v644,v646,v648,v649,v651,v652,v654,v655,v657,v658,v659,v660,v661,v662,v663,v664,v665,v666,v667,v668,v669,v670,v671,v672,v673,v674,v362,v675,v676,v677,v678,v679,v680,v681,v682,v683,v684,v686,v697,v698,v699,v700,v701,v702,v703,v704,v705,v706,v707,v708,v709,v710,v711,v712,v713,v714,v715,v716,v717,v718,v719,v721,v723,v725,v726,v728,v729,v731,v732,v733,v734,v735,v736,v737,v739,v741,v743,v745,v746,v747,v794,v796,v797,v798,v800,v801,v802,v803,v804,v805,v806,v807,v808,v809,v810,v811,v813]) (consBan b639 (consBan b120 (consBan b575 (consBan b640 (consBan b641 (consBan b642 (consBan b643 (consBan b644 (consBan b646 (consBan b648 (consBan b650 (consBan b652 (consBan b654 (consBan b655 (consBan b657 (consBan b658 (consBan b660 (consBan b661 (consBan b663 (consBan b664 (consBan b665 (consBan b666 (consBan b667 (consBan b668 (consBan b669 (consBan b670 (consBan b671 (consBan b673 (consBan b674 (consBan b675 (consBan b676 (consBan b677 (consBan b678 (consBan b679 (consBan b680 (consBan b681 (consBan b682 (consBan b363 (consBan b683 (consBan b684 (consBan b685 (consBan b686 (consBan b687 (consBan b688 (consBan b689 (consBan b690 (consBan b691 (consBan b693 (consBan b704 (consBan b705 (consBan b706 (consBan b707 (consBan b708 (consBan b709 (consBan b710 (consBan b711 (consBan b712 (consBan b713 (consBan b714 (consBan b715 (consBan b716 (consBan b717 (consBan b718 (consBan b719 (consBan b720 (consBan b721 (consBan b722 (consBan b723 (consBan b724 (consBan b725 (consBan b726 (consBan b728 (consBan b730 (consBan b732 (consBan b733 (consBan b735 (consBan b736 (consBan b738 (consBan b739 (consBan b740 (consBan b741 (consBan b742 (consBan b743 (consBan b744 (consBan b746 (consBan b748 (consBan b750 (consBan b752 (consBan b753 (consBan b754 (consBan b801 (consBan b803 (consBan b804 (consBan b805 (consBan b807 (consBan b808 (consBan b809 (consBan b810 (consBan b811 (consBan b812 (consBan b813 (consBan b814 (consBan b815 (consBan b816 (consBan b817 (consBan b818 (consBan b820 (consBan b821 (nilBan 46 7))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b823 : Ban 46 7 v814 := smallByCut p63_42 w13
theorem b824 : Ban 46 7 v630 := smallByCut p63_42 w13
theorem b825 : Ban 46 7 v815 := smallByCut p63_42 w13
theorem b826 : Ban 46 7 v816 := smallByCut p63_21 w13
theorem b827 : Ban 46 7 v817 := smallByCut p63_21 w13
theorem b852 : Ban 46 7 v818 := smallByCut p63_61 w12
theorem b853 : Ban 46 7 v842 := smallByCut p63_42 w13
theorem b854 : Ban 46 7 v843 := smallByCut p63_42 w13
theorem b856 : Ban 46 7 v844 := smallByCut p63_21 w13
theorem b857 : Ban 46 7 v846 := smallByCut p63_21 w13
theorem b858 : Ban 46 7 v847 := smallByCut p63_21 w13
theorem b859 : Ban 46 7 v848 := smallByCut p63_21 w13
theorem b860 : Ban 46 7 v849 := smallByCut p63_55 w12
theorem b861 : Ban 46 7 v850 := smallByCut p63_42 w13
theorem b862 : Ban 46 7 v851 := smallByCut p63_42 w13
theorem b863 : Ban 46 7 v852 := smallByCut p63_42 w13
theorem b864 : Ban 46 7 v853 := smallByCut p63_21 w13
theorem b865 : Ban 46 7 v854 := smallByCut p63_21 w13
theorem b866 : Ban 46 7 v629 := smallByCut p63_42 w13
theorem b868 : Ban 46 7 v855 := smallByCut p63_42 w13
theorem b869 : Ban 46 7 v857 := smallByCut p63_42 w13
theorem b870 : Ban 46 7 v858 := smallByCut p63_42 w13
theorem b871 : Ban 46 7 v859 := smallByCut p63_42 w13
theorem b872 : Ban 46 7 v860 := smallByCut p63_42 w13
theorem b873 : Ban 46 7 v861 := smallByCut p63_42 w13
theorem b653 : Ban 46 7 v647 := smallByCut p63_42 w13
theorem b875 : Ban 46 7 v862 := smallByCut p63_42 w13
theorem b876 : Ban 46 7 v863 := smallByCut p63_42 w13
theorem b877 : Ban 46 7 v864 := smallByCut p63_21 w13
theorem b878 : Ban 46 7 v865 := smallByCut p63_21 w13
theorem b880 : Ban 46 7 v866 := smallByCut p63_47 w3
theorem b881 : Ban 46 7 v868 := smallByCut p63_42 w13
theorem b416 : Ban 46 7 v416 := smallByCut p63_42 w13
theorem b882 : Ban 46 7 v869 := smallByCut p63_42 w13
theorem b884 : Ban 46 7 v870 := smallByCut p63_21 w13
theorem b885 : Ban 46 7 v872 := smallByCut p63_21 w13
theorem b886 : Ban 46 7 v873 := smallByCut p63_21 w13
theorem b887 : Ban 46 7 v874 := smallByCut p63_21 w13
theorem b888 : Ban 46 7 v875 := smallByCut p63_21 w13
theorem b889 : Ban 46 7 v876 := smallByCut p63_42 w13
theorem b890 : Ban 46 7 v877 := smallByCut p63_42 w13
theorem b891 : Ban 46 7 v878 := smallByCut p63_21 w13
theorem b892 : Ban 46 7 v879 := smallByCut p63_42 w13
theorem b893 : Ban 46 7 v880 := smallByCut p63_42 w13
theorem b894 : Ban 46 7 v881 := smallByCut p63_47 w12
theorem b895 : Ban 46 7 v882 := smallByCut p63_42 w13
theorem b896 : Ban 46 7 v883 := smallByCut p63_42 w13
theorem b897 : Ban 46 7 v884 := smallByCut p63_42 w13
theorem b898 : Ban 46 7 v885 := smallByCut p63_21 w13
theorem b899 : Ban 46 7 v886 := smallByCut p63_42 w13
theorem b900 : Ban 46 7 v887 := smallByCut p63_42 w13
theorem b901 : Ban 46 7 v888 := smallByCut p63_21 w13
theorem b903 : Ban 46 7 v889 := smallByCut p63_21 w13
theorem b904 : Ban 46 7 v891 := smallByCut p63_21 w13
theorem b905 : Ban 46 7 v892 := smallByCut p63_21 w13
theorem b906 : Ban 46 7 v893 := smallByCut p63_21 w13
theorem b907 : Ban 46 7 v894 := smallByCut p63_21 w13
theorem b908 : Ban 46 7 v895 := smallByCut p63_42 w13
theorem b909 : Ban 46 7 v896 := smallByCut p63_21 w13
theorem b910 : Ban 46 7 v897 := smallByCut p63_42 w13
theorem b911 : Ban 46 7 v898 := smallByCut p63_21 w13
theorem b912 : Ban 46 7 v899 := smallByCut p63_42 w13
theorem b913 : Ban 46 7 v900 := smallByCut p63_21 w13
theorem b914 : Ban 46 7 v901 := smallByCut p63_42 w13
theorem b916 : Ban 46 7 v902 := smallByCut p63_21 w13
theorem b917 : Ban 46 7 v904 := smallByCut p63_21 w13
theorem b918 : Ban 46 7 v905 := smallByCut p63_21 w13
theorem b919 : Ban 46 7 v906 := smallByCut p63_21 w13
theorem b920 : Ban 46 7 v907 := smallByCut p63_21 w13
theorem b921 : Ban 46 7 v908 := smallByCut p63_42 w13
theorem b922 : Ban 46 7 v909 := smallByCut p63_21 w13
theorem b923 : Ban 46 7 v910 := smallByCut p63_42 w13
theorem b924 : Ban 46 7 v911 := smallByCut p63_21 w13
theorem b925 : Ban 46 7 v912 := smallByCut p63_42 w13
theorem b926 : Ban 46 7 v913 := smallByCut p63_21 w13
theorem b927 : Ban 46 7 v914 := smallByCut p63_42 w13
theorem b928 : Ban 46 7 v915 := smallByCut p63_21 w13
theorem b929 : Ban 46 7 v916 := smallByCut p63_21 w13
theorem b930 : Ban 46 7 v917 := smallByCut p63_21 w13
theorem b931 : Ban 46 7 v918 := smallByCut p63_21 w13
theorem b933 : Ban 46 7 v919 := smallByCut p63_42 w13
theorem b935 : Ban 46 7 v921 := smallByCut p63_42 w13
theorem b936 : Ban 46 7 v923 := smallByCut p63_42 w13
theorem b937 : Ban 46 7 v924 := smallByCut p63_42 w13
theorem b938 : Ban 46 7 v925 := smallByCut p63_42 w13
theorem b939 : Ban 46 7 v926 := smallByCut p63_42 w13
theorem b940 : Ban 46 7 v927 := smallByCut p63_21 w13
theorem b432 : Ban 46 7 v432 := smallByCut p63_42 w13
theorem b941 : Ban 46 7 v928 := smallByCut p63_42 w13
theorem b942 : Ban 46 7 v929 := smallByCut p63_21 w13
theorem b943 : Ban 46 7 v930 := smallByCut p63_21 w13
theorem b944 : Ban 46 7 v931 := smallByCut p63_42 w13
theorem b945 : Ban 46 7 v932 := smallByCut p63_42 w13
theorem b946 : Ban 46 7 v933 := smallByCut p63_21 w13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b947 : Ban 46 8 v720 := viaBranch (ws := [v814,v630,v815,v816,v817,v818,v842,v542,v843,v844,v846,v847,v848,v849,v850,v851,v852,v853,v854,v629,v855,v857,v858,v859,v860,v652,v861,v647,v862,v863,v864,v865,v866,v868,v416,v869,v870,v872,v873,v127,v574,v874,v875,v876,v877,v878,v658,v659,v879,v880,v881,v882,v883,v884,v885,v886,v887,v888,v889,v891,v892,v893,v894,v895,v896,v897,v898,v899,v900,v901,v902,v904,v905,v906,v907,v908,v909,v910,v911,v912,v913,v914,v915,v916,v917,v918,v919,v921,v923,v924,v925,v926,v927,v432,v928,v929,v930,v931,v932,v933]) (consBan b823 (consBan b824 (consBan b825 (consBan b826 (consBan b827 (consBan b852 (consBan b853 (consBan b547 (consBan b854 (consBan b856 (consBan b857 (consBan b858 (consBan b859 (consBan b860 (consBan b861 (consBan b862 (consBan b863 (consBan b864 (consBan b865 (consBan b866 (consBan b868 (consBan b869 (consBan b870 (consBan b871 (consBan b872 (consBan b660 (consBan b873 (consBan b653 (consBan b875 (consBan b876 (consBan b877 (consBan b878 (consBan b880 (consBan b881 (consBan b416 (consBan b882 (consBan b884 (consBan b885 (consBan b886 (consBan b125 (consBan b579 (consBan b887 (consBan b888 (consBan b889 (consBan b890 (consBan b891 (consBan b665 (consBan b666 (consBan b892 (consBan b893 (consBan b894 (consBan b895 (consBan b896 (consBan b897 (consBan b898 (consBan b899 (consBan b900 (consBan b901 (consBan b903 (consBan b904 (consBan b905 (consBan b906 (consBan b907 (consBan b908 (consBan b909 (consBan b910 (consBan b911 (consBan b912 (consBan b913 (consBan b914 (consBan b916 (consBan b917 (consBan b918 (consBan b919 (consBan b920 (consBan b921 (consBan b922 (consBan b923 (consBan b924 (consBan b925 (consBan b926 (consBan b927 (consBan b928 (consBan b929 (consBan b930 (consBan b931 (consBan b933 (consBan b935 (consBan b936 (consBan b937 (consBan b938 (consBan b939 (consBan b940 (consBan b432 (consBan b941 (consBan b942 (consBan b943 (consBan b944 (consBan b945 (consBan b946 (nilBan 46 7))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b948 : Ban 46 8 v719 := viaPerm map63_1 map63_1 b947 (by decide +kernel) (by decide +kernel)
theorem b950 : Ban 46 8 v652 := smallByCut p63_59 w12
theorem b637 : Ban 46 8 v630 := smallByCut p63_47 w12
theorem b951 : Ban 46 8 v862 := viaPerm map63_1 map63_1 b822 (by decide +kernel) (by decide +kernel)
theorem b952 : Ban 46 8 v934 := smallByCut p63_47 w12
theorem b953 : Ban 46 7 v936 := smallByCut p63_21 w13
theorem b954 : Ban 46 7 v937 := smallByCut p63_42 w13
theorem b955 : Ban 46 7 v938 := smallByCut p63_21 w13
theorem b956 : Ban 46 7 v939 := smallByCut p63_21 w13
theorem b958 : Ban 46 7 v940 := smallByCut p63_21 w13
theorem b959 : Ban 46 6 v943 := smallByCut p63_21 w13
theorem b960 : Ban 46 6 v944 := smallByCut p63_21 w13
theorem b961 : Ban 46 6 v945 := smallByCut p63_21 w13
theorem b962 : Ban 46 6 v946 := smallByCut p63_21 w13
theorem b963 : Ban 46 6 v947 := smallByCut p63_21 w13
theorem b964 : Ban 46 6 v948 := smallByCut p63_21 w13
theorem b965 : Ban 46 6 v949 := smallByCut p63_21 w13
theorem b966 : Ban 46 6 v950 := smallByCut p63_21 w13
theorem b967 : Ban 46 6 v951 := smallByCut p63_42 w13
theorem b968 : Ban 46 6 v952 := smallByCut p63_42 w13
theorem b969 : Ban 46 6 v953 := smallByCut p63_42 w13
theorem b970 : Ban 46 6 v954 := smallByCut p63_42 w13
theorem b971 : Ban 46 6 v955 := smallByCut p63_42 w13
theorem b972 : Ban 46 6 v956 := smallByCut p63_21 w13
theorem b973 : Ban 46 6 v957 := smallByCut p63_42 w13
theorem b974 : Ban 46 6 v958 := smallByCut p63_21 w13
theorem b975 : Ban 46 6 v959 := smallByCut p63_42 w13
theorem b976 : Ban 46 6 v960 := smallByCut p63_21 w13
theorem b977 : Ban 46 6 v961 := smallByCut p63_21 w13
theorem b978 : Ban 46 6 v962 := smallByCut p63_21 w13
theorem b979 : Ban 46 6 v963 := smallByCut p63_21 w13
theorem b980 : Ban 46 6 v964 := smallByCut p63_21 w13
theorem b981 : Ban 46 6 v965 := smallByCut p63_21 w13
theorem b982 : Ban 46 6 v966 := smallByCut p63_21 w13
theorem b983 : Ban 46 6 v967 := smallByCut p63_21 w13
theorem b984 : Ban 46 6 v968 := smallByCut p63_21 w13
theorem b985 : Ban 46 6 v969 := smallByCut p63_21 w13
theorem b986 : Ban 46 6 v970 := smallByCut p63_21 w13
theorem b987 : Ban 46 6 v971 := smallByCut p63_21 w13
theorem b988 : Ban 46 6 v972 := smallByCut p63_21 w13
theorem b989 : Ban 46 6 v973 := smallByCut p63_21 w13
theorem b990 : Ban 46 6 v974 := smallByCut p63_21 w13
theorem b991 : Ban 46 6 v975 := smallByCut p63_21 w13
theorem b992 : Ban 46 6 v976 := smallByCut p63_21 w13
theorem b993 : Ban 46 6 v977 := smallByCut p63_21 w13
theorem b994 : Ban 46 6 v978 := smallByCut p63_21 w13
theorem b995 : Ban 46 6 v979 := smallByCut p63_21 w13
theorem b996 : Ban 46 6 v980 := smallByCut p63_21 w13
theorem b997 : Ban 46 6 v981 := smallByCut p63_21 w13
theorem b998 : Ban 46 6 v982 := smallByCut p63_21 w13
theorem b999 : Ban 46 6 v983 := smallByCut p63_21 w13
theorem b1000 : Ban 46 6 v984 := smallByCut p63_21 w13
theorem b1001 : Ban 46 6 v985 := smallByCut p63_21 w13
theorem b1002 : Ban 46 6 v986 := smallByCut p63_21 w13
theorem b1003 : Ban 46 6 v987 := smallByCut p63_21 w13
theorem b1004 : Ban 46 6 v988 := smallByCut p63_21 w13
theorem b1005 : Ban 46 6 v989 := smallByCut p63_21 w13
theorem b1006 : Ban 46 6 v990 := smallByCut p63_21 w13
theorem b1007 : Ban 46 6 v991 := smallByCut p63_21 w13
theorem b1008 : Ban 46 6 v992 := smallByCut p63_42 w13
theorem b1009 : Ban 46 6 v993 := smallByCut p63_42 w13
theorem b1010 : Ban 46 6 v994 := smallByCut p63_42 w13
theorem b1011 : Ban 46 6 v995 := smallByCut p63_42 w13
theorem b1012 : Ban 46 6 v996 := smallByCut p63_21 w13
theorem b1013 : Ban 46 6 v997 := smallByCut p63_21 w13
theorem b1014 : Ban 46 6 v998 := smallByCut p63_21 w13
theorem b1015 : Ban 46 6 v999 := smallByCut p63_21 w13
theorem b1016 : Ban 46 6 v1000 := smallByCut p63_21 w13
theorem b1017 : Ban 46 6 v1001 := smallByCut p63_21 w13
theorem b1018 : Ban 46 6 v1002 := smallByCut p63_21 w13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1019 : Ban 46 7 v289 := viaBranch (ws := [v943,v944,v945,v946,v947,v948,v949,v950,v951,v952,v953,v954,v955,v290,v956,v957,v958,v959,v960,v961,v962,v963,v964,v965,v966,v967,v968,v969,v970,v971,v972,v973,v974,v975,v976,v977,v978,v979,v980,v981,v982,v983,v984,v985,v986,v987,v988,v989,v990,v991,v992,v993,v994,v995,v996,v997,v998,v999,v1000,v291,v1001,v1002]) (consBan b959 (consBan b960 (consBan b961 (consBan b962 (consBan b963 (consBan b964 (consBan b965 (consBan b966 (consBan b967 (consBan b968 (consBan b969 (consBan b970 (consBan b971 (consBan b288 (consBan b972 (consBan b973 (consBan b974 (consBan b975 (consBan b976 (consBan b977 (consBan b978 (consBan b979 (consBan b980 (consBan b981 (consBan b982 (consBan b983 (consBan b984 (consBan b985 (consBan b986 (consBan b987 (consBan b988 (consBan b989 (consBan b990 (consBan b991 (consBan b992 (consBan b993 (consBan b994 (consBan b995 (consBan b996 (consBan b997 (consBan b998 (consBan b999 (consBan b1000 (consBan b1001 (consBan b1002 (consBan b1003 (consBan b1004 (consBan b1005 (consBan b1006 (consBan b1007 (consBan b1008 (consBan b1009 (consBan b1010 (consBan b1011 (consBan b1012 (consBan b1013 (consBan b1014 (consBan b1015 (consBan b1016 (consBan b289 (consBan b1017 (consBan b1018 (nilBan 46 6))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1020 : Ban 46 7 v942 := viaPerm map63_5 map63_6 b1019 (by decide +kernel) (by decide +kernel)
theorem b1022 : Ban 46 7 v1003 := smallByCut p63_21 w13
theorem b1023 : Ban 46 7 v1004 := smallByCut p63_21 w13
theorem b1024 : Ban 46 7 v1005 := smallByCut p63_21 w13
theorem b1026 : Ban 46 7 v1006 := smallByCut p63_21 w13
theorem b1027 : Ban 46 7 v1008 := smallByCut p63_61 w12
theorem b1028 : Ban 46 7 v1009 := smallByCut p63_21 w13
theorem b1029 : Ban 46 7 v1010 := smallByCut p63_21 w13
theorem b1030 : Ban 46 7 v1011 := smallByCut p63_21 w13
theorem b1031 : Ban 46 7 v1012 := smallByCut p63_21 w13
theorem b1032 : Ban 46 7 v1013 := smallByCut p63_21 w13
theorem b1033 : Ban 46 7 v1014 := viaPerm map63_4 map63_4 b1019 (by decide +kernel) (by decide +kernel)
theorem b1034 : Ban 46 7 v1015 := smallByCut p63_21 w13
theorem b1035 : Ban 46 7 v1016 := smallByCut p63_21 w13
theorem b1036 : Ban 46 7 v1017 := smallByCut p63_21 w13
theorem b551 : Ban 46 7 v547 := smallByCut p63_21 w13
theorem b1025 : Ban 46 7 v1007 := smallByCut p63_21 w13
theorem b1037 : Ban 46 7 v1018 := smallByCut p63_55 w12
theorem b1038 : Ban 46 7 v1019 := smallByCut p63_21 w13
theorem b1039 : Ban 46 7 v1020 := smallByCut p63_21 w13
theorem b1040 : Ban 46 7 v1021 := smallByCut p63_21 w13
theorem b1041 : Ban 46 7 v1022 := smallByCut p63_21 w13
theorem b1042 : Ban 46 7 v1023 := smallByCut p63_21 w13
theorem b1043 : Ban 46 7 v1024 := viaPerm map63_1 map63_1 b1019 (by decide +kernel) (by decide +kernel)
theorem b1044 : Ban 46 7 v1025 := smallByCut p63_21 w13
theorem b1045 : Ban 46 7 v1026 := smallByCut p63_42 w13
theorem b1046 : Ban 46 7 v1027 := smallByCut p63_21 w13
theorem b1047 : Ban 46 7 v1028 := smallByCut p63_21 w13
theorem b1048 : Ban 46 7 v1029 := smallByCut p63_21 w13
theorem b1049 : Ban 46 7 v1030 := smallByCut p63_59 w12
theorem b1050 : Ban 46 7 v1031 := smallByCut p63_21 w13
theorem b1051 : Ban 46 7 v1032 := smallByCut p63_42 w13
theorem b1052 : Ban 46 7 v1033 := smallByCut p63_21 w13
theorem b1053 : Ban 46 7 v1034 := smallByCut p63_21 w13
theorem b957 : Ban 46 7 v941 := smallByCut p63_21 w13
theorem b1021 : Ban 46 7 v958 := smallByCut p63_21 w13
theorem b1054 : Ban 46 7 v1035 := smallByCut p63_42 w13
theorem b1055 : Ban 46 7 v1036 := smallByCut p63_21 w13
theorem b1056 : Ban 46 7 v1037 := smallByCut p63_21 w13
theorem b1057 : Ban 46 7 v1038 := smallByCut p63_47 w12
theorem b1058 : Ban 46 7 v1039 := smallByCut p63_21 w13
theorem b1059 : Ban 46 7 v1040 := smallByCut p63_42 w13
theorem b1060 : Ban 46 7 v1041 := smallByCut p63_21 w13
theorem b1061 : Ban 46 7 v1042 := smallByCut p63_21 w13
theorem b1062 : Ban 46 7 v1043 := smallByCut p63_21 w13
theorem b1063 : Ban 46 7 v1044 := smallByCut p63_21 w13
theorem b1065 : Ban 46 7 v1045 := smallByCut p63_21 w13
theorem b1066 : Ban 46 7 v1047 := smallByCut p63_21 w13
theorem b1067 : Ban 46 7 v1048 := smallByCut p63_21 w13
theorem b1068 : Ban 46 7 v1049 := smallByCut p63_21 w13
theorem b1069 : Ban 46 7 v1050 := smallByCut p63_21 w13
theorem b1070 : Ban 46 7 v1051 := smallByCut p63_21 w13
theorem b1072 : Ban 46 7 v1052 := smallByCut p63_42 w13
theorem b1073 : Ban 46 7 v1054 := smallByCut p63_42 w13
theorem b1074 : Ban 46 7 v1055 := smallByCut p63_42 w13
theorem b1071 : Ban 46 7 v1053 := smallByCut p63_42 w13
theorem b1075 : Ban 46 7 v1056 := smallByCut p63_42 w13
theorem b1076 : Ban 46 7 v1057 := smallByCut p63_42 w13
theorem b1077 : Ban 12 4 v1060 := checkedSmall
theorem b1078 : Ban 12 4 v1061 := checkedSmall
theorem b1079 : Ban 12 4 v1062 := checkedSmall
theorem b1080 : Ban 12 4 v1063 := checkedSmall
theorem b1081 : Ban 12 4 v1064 := checkedSmall
theorem b1082 : Ban 12 4 v1065 := checkedSmall
theorem b1083 : Ban 12 4 v1066 := checkedSmall
theorem b1084 : Ban 12 4 v1067 := checkedSmall
theorem b1085 : Ban 12 4 v1068 := checkedSmall
theorem b1086 : Ban 12 4 v1069 := checkedSmall
theorem b1087 : Ban 12 4 v1070 := checkedSmall
theorem b1088 : Ban 12 4 v1071 := checkedSmall
theorem b1089 : Ban 12 4 v1072 := checkedSmall
theorem b1090 : Ban 12 4 v1073 := checkedSmall
theorem b1091 : Ban 12 4 v1074 := checkedSmall
theorem b1092 : Ban 12 4 v1075 := checkedSmall
theorem b1093 : Ban 12 4 v1076 := checkedSmall
theorem b1094 : Ban 12 4 v1077 := checkedSmall
theorem b1095 : Ban 12 4 v1078 := checkedSmall
theorem b1096 : Ban 12 4 v1079 := checkedSmall
theorem b1097 : Ban 12 4 v1080 := checkedSmall
theorem b1098 : Ban 12 4 v1081 := checkedSmall
theorem b1099 : Ban 12 4 v1082 := checkedSmall
theorem b1100 : Ban 12 4 v1083 := checkedSmall
theorem b1101 : Ban 12 4 v1084 := checkedSmall
theorem b1102 : Ban 12 4 v1085 := checkedSmall
theorem b1103 : Ban 12 4 v1086 := checkedSmall
theorem b1104 : Ban 12 4 v1087 := checkedSmall
theorem b1105 : Ban 12 4 v1088 := checkedSmall
theorem b1106 : Ban 12 4 v1089 := checkedSmall
theorem b1107 : Ban 12 4 v1090 := checkedSmall
theorem b1108 : Ban 12 4 v1091 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1109 : Ban 12 5 v1059 := viaBranch (ws := [v1060,v1061,v1062,v1063,v1064,v1065,v1066,v1067,v1068,v1069,v1070,v1071,v1072,v1073,v1074,v1075,v1076,v1077,v1078,v1079,v1080,v1081,v1082,v1083,v1084,v1085,v1086,v1087,v1088,v1089,v1090,v1091]) (consBan b1077 (consBan b1078 (consBan b1079 (consBan b1080 (consBan b1081 (consBan b1082 (consBan b1083 (consBan b1084 (consBan b1085 (consBan b1086 (consBan b1087 (consBan b1088 (consBan b1089 (consBan b1090 (consBan b1091 (consBan b1092 (consBan b1093 (consBan b1094 (consBan b1095 (consBan b1096 (consBan b1097 (consBan b1098 (consBan b1099 (consBan b1100 (consBan b1101 (consBan b1102 (consBan b1103 (consBan b1104 (consBan b1105 (consBan b1106 (consBan b1107 (consBan b1108 (nilBan 12 4))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w14 : Wide 12 5 v1059 := viaSub (ws := [v1059]) (consBan b1109 (nilBan 12 5)) (by decide) (by decide +kernel)
theorem b1110 : Ban 46 7 v1058 := smallByCut p63_39 w14
theorem b1111 : Ban 46 7 v1092 := smallByCut p63_42 w13
theorem b1112 : Ban 46 7 v1093 := smallByCut p63_21 w13
theorem b1113 : Ban 46 7 v1094 := smallByCut p63_21 w13
theorem b1114 : Ban 46 7 v1095 := smallByCut p63_21 w13
theorem b1116 : Ban 46 7 v1096 := smallByCut p63_21 w13
theorem b1117 : Ban 46 7 v1098 := smallByCut p63_21 w13
theorem b1118 : Ban 46 7 v1099 := smallByCut p63_21 w13
theorem b1119 : Ban 46 7 v1100 := smallByCut p63_21 w13
theorem b1120 : Ban 46 7 v1101 := smallByCut p63_21 w13
theorem b1121 : Ban 46 7 v1102 := smallByCut p63_21 w13
theorem b1122 : Ban 46 7 v1103 := smallByCut p63_21 w13
theorem b1123 : Ban 46 7 v1104 := smallByCut p63_21 w13
theorem b1124 : Ban 46 7 v1105 := smallByCut p63_21 w13
theorem b1125 : Ban 46 7 v1106 := smallByCut p63_21 w13
theorem b1126 : Ban 46 7 v1107 := smallByCut p63_21 w13
theorem b1127 : Ban 46 7 v1108 := smallByCut p63_21 w13
theorem b1128 : Ban 46 7 v1109 := smallByCut p63_21 w13
theorem b1129 : Ban 46 7 v1110 := smallByCut p63_21 w13
theorem b1130 : Ban 46 7 v1111 := smallByCut p63_21 w13
theorem b1131 : Ban 46 7 v1112 := smallByCut p63_21 w13
theorem b1132 : Ban 46 7 v1113 := smallByCut p63_21 w13
theorem b1133 : Ban 46 7 v1114 := smallByCut p63_21 w13
theorem b1134 : Ban 46 7 v1115 := smallByCut p63_21 w13
theorem b1135 : Ban 46 7 v1116 := smallByCut p63_21 w13
theorem b1136 : Ban 46 7 v1117 := smallByCut p63_21 w13
theorem b1137 : Ban 46 7 v1118 := smallByCut p63_21 w13
theorem b1138 : Ban 46 7 v1119 := smallByCut p63_21 w13
theorem b1139 : Ban 46 7 v1120 := smallByCut p63_21 w13
theorem b1140 : Ban 46 7 v1121 := smallByCut p63_21 w13
theorem b1141 : Ban 46 7 v1122 := smallByCut p63_21 w13
theorem b1142 : Ban 46 7 v1123 := smallByCut p63_21 w13
theorem b1143 : Ban 46 7 v1124 := smallByCut p63_42 w13
theorem b1115 : Ban 46 7 v1097 := smallByCut p63_42 w13
theorem b1144 : Ban 46 7 v1125 := smallByCut p63_42 w13
theorem b1145 : Ban 46 7 v1126 := smallByCut p63_42 w13
theorem b1064 : Ban 46 7 v1046 := smallByCut p63_21 w13
theorem b1146 : Ban 46 7 v1127 := smallByCut p63_21 w13
theorem b1147 : Ban 46 7 v1128 := smallByCut p63_21 w13
theorem b1148 : Ban 46 7 v1129 := smallByCut p63_21 w13
theorem b1149 : Ban 46 7 v1130 := smallByCut p63_21 w13
theorem b1150 : Ban 46 7 v1131 := smallByCut p63_21 w13
theorem b1151 : Ban 46 7 v1132 := smallByCut p63_21 w13
theorem b1152 : Ban 46 7 v1133 := smallByCut p63_21 w13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1153 : Ban 46 8 v935 := viaBranch (ws := [v936,v937,v938,v939,v940,v942,v1003,v1004,v1005,v546,v1006,v1008,v1009,v1010,v1011,v1012,v1013,v1014,v1015,v1016,v1017,v547,v1007,v1018,v1019,v1020,v1021,v1022,v1023,v1024,v1025,v1026,v1027,v1028,v1029,v1030,v1031,v1032,v1033,v1034,v941,v289,v958,v1035,v1036,v864,v1037,v1038,v1039,v1040,v1041,v1042,v1043,v1044,v1045,v129,v576,v1047,v1048,v1049,v1050,v1051,v1052,v661,v1054,v1055,v1053,v1056,v885,v1057,v1058,v1092,v1093,v1094,v1095,v1096,v1098,v1099,v1100,v1101,v1102,v1103,v1104,v1105,v1106,v1107,v1108,v1109,v1110,v1111,v1112,v1113,v1114,v1115,v1116,v1117,v1118,v1119,v1120,v1121,v1122,v1123,v1124,v1097,v1125,v1126,v1046,v1127,v1128,v1129,v1130,v1131,v1132,v1133]) (consBan b953 (consBan b954 (consBan b955 (consBan b956 (consBan b958 (consBan b1020 (consBan b1022 (consBan b1023 (consBan b1024 (consBan b552 (consBan b1026 (consBan b1027 (consBan b1028 (consBan b1029 (consBan b1030 (consBan b1031 (consBan b1032 (consBan b1033 (consBan b1034 (consBan b1035 (consBan b1036 (consBan b551 (consBan b1025 (consBan b1037 (consBan b1038 (consBan b1039 (consBan b1040 (consBan b1041 (consBan b1042 (consBan b1043 (consBan b1044 (consBan b1045 (consBan b1046 (consBan b1047 (consBan b1048 (consBan b1049 (consBan b1050 (consBan b1051 (consBan b1052 (consBan b1053 (consBan b957 (consBan b1019 (consBan b1021 (consBan b1054 (consBan b1055 (consBan b877 (consBan b1056 (consBan b1057 (consBan b1058 (consBan b1059 (consBan b1060 (consBan b1061 (consBan b1062 (consBan b1063 (consBan b1065 (consBan b127 (consBan b581 (consBan b1066 (consBan b1067 (consBan b1068 (consBan b1069 (consBan b1070 (consBan b1072 (consBan b668 (consBan b1073 (consBan b1074 (consBan b1071 (consBan b1075 (consBan b898 (consBan b1076 (consBan b1110 (consBan b1111 (consBan b1112 (consBan b1113 (consBan b1114 (consBan b1116 (consBan b1117 (consBan b1118 (consBan b1119 (consBan b1120 (consBan b1121 (consBan b1122 (consBan b1123 (consBan b1124 (consBan b1125 (consBan b1126 (consBan b1127 (consBan b1128 (consBan b1129 (consBan b1130 (consBan b1131 (consBan b1132 (consBan b1133 (consBan b1134 (consBan b1135 (consBan b1136 (consBan b1137 (consBan b1138 (consBan b1139 (consBan b1140 (consBan b1141 (consBan b1142 (consBan b1143 (consBan b1115 (consBan b1144 (consBan b1145 (consBan b1064 (consBan b1146 (consBan b1147 (consBan b1148 (consBan b1149 (consBan b1150 (consBan b1151 (consBan b1152 (nilBan 46 7))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1154 : Ban 46 7 v1135 := smallByCut p63_21 w13
theorem b1155 : Ban 46 7 v1136 := smallByCut p63_21 w13
theorem b1156 : Ban 46 7 v1137 := smallByCut p63_21 w13
theorem b1157 : Ban 46 7 v1138 := smallByCut p63_55 w3
theorem b1158 : Ban 46 7 v1139 := smallByCut p63_55 w3
theorem b1159 : Ban 46 7 v1140 := smallByCut p63_55 w3
theorem b1160 : Ban 46 7 v1141 := smallByCut p63_42 w13
theorem b1161 : Ban 46 7 v1142 := smallByCut p63_21 w13
theorem b1162 : Ban 46 7 v1143 := smallByCut p63_42 w13
theorem b1163 : Ban 46 7 v1144 := smallByCut p63_42 w13
theorem b1164 : Ban 46 7 v1145 := smallByCut p63_42 w13
theorem b1165 : Ban 46 7 v1146 := smallByCut p63_42 w13
theorem b1166 : Ban 46 7 v1147 := smallByCut p63_42 w13
theorem b1167 : Ban 46 7 v1148 := smallByCut p63_42 w13
theorem b1168 : Ban 46 7 v1149 := smallByCut p63_42 w13
theorem b1169 : Ban 46 7 v1150 := smallByCut p63_42 w13
theorem b1170 : Ban 46 7 v1151 := smallByCut p63_21 w13
theorem b1171 : Ban 46 7 v1152 := smallByCut p63_21 w13
theorem b1172 : Ban 46 7 v1153 := smallByCut p63_21 w13
theorem b1173 : Ban 46 7 v1154 := smallByCut p63_21 w13
theorem b1174 : Ban 46 7 v1155 := smallByCut p63_21 w13
theorem b1175 : Ban 46 7 v1156 := smallByCut p63_21 w13
theorem b1176 : Ban 46 7 v1157 := smallByCut p63_21 w13
theorem b1177 : Ban 46 7 v1158 := smallByCut p63_59 w3
theorem b1178 : Ban 46 7 v1159 := smallByCut p63_21 w13
theorem b1179 : Ban 46 7 v1160 := smallByCut p63_42 w13
theorem b1180 : Ban 46 7 v1161 := smallByCut p63_21 w13
theorem b1181 : Ban 46 7 v1162 := smallByCut p63_47 w3
theorem b1182 : Ban 46 7 v1163 := smallByCut p63_21 w13
theorem b1183 : Ban 46 7 v1164 := smallByCut p63_42 w13
theorem b1184 : Ban 46 7 v1165 := smallByCut p63_21 w13
theorem b1185 : Ban 46 7 v1166 := smallByCut p63_21 w13
theorem b1186 : Ban 46 7 v1167 := smallByCut p63_21 w13
theorem b1187 : Ban 46 7 v1168 := smallByCut p63_21 w13
theorem b1189 : Ban 46 7 v1169 := smallByCut p63_21 w13
theorem b1190 : Ban 46 7 v1171 := smallByCut p63_21 w13
theorem b1191 : Ban 46 7 v1172 := smallByCut p63_61 w3
theorem b1192 : Ban 46 7 v1173 := smallByCut p63_21 w13
theorem b1193 : Ban 46 7 v1174 := smallByCut p63_21 w13
theorem b1195 : Ban 46 7 v1175 := smallByCut p63_61 w3
theorem b1196 : Ban 46 7 v1177 := smallByCut p63_61 w3
theorem b1197 : Ban 46 7 v1178 := smallByCut p63_21 w13
theorem b1198 : Ban 46 7 v1179 := smallByCut p63_55 w3
theorem b1199 : Ban 46 7 v1180 := smallByCut p63_21 w13
theorem b1200 : Ban 46 7 v1181 := smallByCut p63_42 w13
theorem b1201 : Ban 46 7 v1182 := smallByCut p63_21 w13
theorem b1202 : Ban 46 7 v1183 := smallByCut p63_47 w3
theorem b1203 : Ban 46 7 v1184 := smallByCut p63_21 w13
theorem b1204 : Ban 46 7 v1185 := smallByCut p63_42 w13
theorem b1205 : Ban 46 7 v1186 := smallByCut p63_21 w13
theorem b1206 : Ban 46 7 v1187 := smallByCut p63_21 w13
theorem b1207 : Ban 46 7 v1188 := smallByCut p63_21 w13
theorem b1208 : Ban 46 7 v1189 := smallByCut p63_21 w13
theorem b1209 : Ban 46 7 v1190 := smallByCut p63_21 w13
theorem b1210 : Ban 46 7 v1191 := smallByCut p63_21 w13
theorem b1211 : Ban 46 7 v1192 := smallByCut p63_55 w3
theorem b1212 : Ban 46 7 v1193 := smallByCut p63_55 w3
theorem b1213 : Ban 46 7 v1194 := smallByCut p63_21 w13
theorem b1214 : Ban 46 7 v1195 := smallByCut p63_21 w13
theorem b1215 : Ban 46 7 v1196 := smallByCut p63_55 w3
theorem b1216 : Ban 46 7 v1197 := smallByCut p63_55 w3
theorem b1217 : Ban 46 7 v1198 := smallByCut p63_42 w13
theorem b1218 : Ban 46 7 v1199 := smallByCut p63_42 w13
theorem b1219 : Ban 46 7 v1200 := smallByCut p63_42 w13
theorem b1220 : Ban 46 7 v1201 := smallByCut p63_42 w13
theorem b1221 : Ban 46 7 v1202 := smallByCut p63_21 w13
theorem b161 : Ban 46 7 v131 := smallByCut p63_59 w3
theorem b1222 : Ban 46 7 v1203 := smallByCut p63_59 w3
theorem b1223 : Ban 46 7 v1204 := smallByCut p63_42 w13
theorem b1224 : Ban 46 7 v1205 := smallByCut p63_59 w3
theorem b1225 : Ban 46 7 v1206 := smallByCut p63_21 w13
theorem b1188 : Ban 46 7 v1170 := smallByCut p63_42 w13
theorem b1226 : Ban 46 7 v1207 := smallByCut p63_42 w13
theorem b1227 : Ban 46 7 v1208 := smallByCut p63_59 w3
theorem b1228 : Ban 46 7 v1209 := smallByCut p63_42 w13
theorem b1229 : Ban 46 7 v1210 := smallByCut p63_42 w13
theorem b1230 : Ban 46 7 v1211 := smallByCut p63_59 w3
theorem b1231 : Ban 46 7 v1212 := smallByCut p63_59 w3
theorem b1232 : Ban 46 7 v1213 := smallByCut p63_21 w13
theorem b1233 : Ban 46 7 v1214 := smallByCut p63_47 w3
theorem b1234 : Ban 46 7 v1215 := smallByCut p63_47 w3
theorem b1235 : Ban 46 7 v1216 := smallByCut p63_42 w13
theorem b1236 : Ban 46 7 v1217 := smallByCut p63_47 w3
theorem b1237 : Ban 46 7 v1218 := smallByCut p63_21 w13
theorem b1238 : Ban 46 7 v1219 := smallByCut p63_42 w13
theorem b1239 : Ban 46 7 v1220 := smallByCut p63_42 w13
theorem b1240 : Ban 46 7 v1221 := smallByCut p63_47 w3
theorem b1241 : Ban 46 7 v1222 := smallByCut p63_47 w3
theorem b1242 : Ban 46 7 v1223 := smallByCut p63_42 w13
theorem b1243 : Ban 46 7 v1224 := smallByCut p63_42 w13
theorem b1194 : Ban 46 7 v1176 := smallByCut p63_47 w3
theorem b1244 : Ban 46 7 v1225 := smallByCut p63_47 w3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1245 : Ban 46 8 v1134 := viaBranch (ws := [v1135,v130,v164,v577,v578,v1136,v1137,v1138,v1139,v1140,v1141,v1142,v1143,v662,v1144,v1145,v1146,v1147,v886,v1148,v1058,v1092,v1093,v1094,v1149,v1150,v1151,v1152,v1043,v1153,v1154,v1155,v1156,v1157,v1158,v1159,v1160,v1161,v1162,v1163,v1164,v1165,v1166,v1167,v1168,v1169,v1171,v411,v1172,v1173,v1174,v1175,v1177,v1178,v1179,v1180,v1181,v1182,v1183,v1184,v1185,v1186,v1187,v1188,v1189,v1190,v1191,v1192,v1193,v1194,v1195,v1196,v1197,v1198,v1199,v1200,v1201,v1202,v131,v1203,v1204,v1205,v1206,v1170,v1207,v803,v1208,v1209,v1210,v1211,v1212,v1213,v1214,v1215,v1216,v1217,v1218,v1219,v1220,v1221,v1222,v1223,v1224,v1176,v1225,v937]) (consBan b1154 (consBan b162 (consBan b163 (consBan b582 (consBan b583 (consBan b1155 (consBan b1156 (consBan b1157 (consBan b1158 (consBan b1159 (consBan b1160 (consBan b1161 (consBan b1162 (consBan b669 (consBan b1163 (consBan b1164 (consBan b1165 (consBan b1166 (consBan b899 (consBan b1167 (consBan b1110 (consBan b1111 (consBan b1112 (consBan b1113 (consBan b1168 (consBan b1169 (consBan b1170 (consBan b1171 (consBan b1062 (consBan b1172 (consBan b1173 (consBan b1174 (consBan b1175 (consBan b1176 (consBan b1177 (consBan b1178 (consBan b1179 (consBan b1180 (consBan b1181 (consBan b1182 (consBan b1183 (consBan b1184 (consBan b1185 (consBan b1186 (consBan b1187 (consBan b1189 (consBan b1190 (consBan b412 (consBan b1191 (consBan b1192 (consBan b1193 (consBan b1195 (consBan b1196 (consBan b1197 (consBan b1198 (consBan b1199 (consBan b1200 (consBan b1201 (consBan b1202 (consBan b1203 (consBan b1204 (consBan b1205 (consBan b1206 (consBan b1207 (consBan b1208 (consBan b1209 (consBan b1210 (consBan b1211 (consBan b1212 (consBan b1213 (consBan b1214 (consBan b1215 (consBan b1216 (consBan b1217 (consBan b1218 (consBan b1219 (consBan b1220 (consBan b1221 (consBan b161 (consBan b1222 (consBan b1223 (consBan b1224 (consBan b1225 (consBan b1188 (consBan b1226 (consBan b811 (consBan b1227 (consBan b1228 (consBan b1229 (consBan b1230 (consBan b1231 (consBan b1232 (consBan b1233 (consBan b1234 (consBan b1235 (consBan b1236 (consBan b1237 (consBan b1238 (consBan b1239 (consBan b1240 (consBan b1241 (consBan b1242 (consBan b1243 (consBan b1194 (consBan b1244 (consBan b954 (nilBan 46 7))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1246 : Ban 46 7 v935 := smallByCut p63_21 w13
theorem b1247 : Ban 46 7 v1226 := smallByCut p63_21 w13
theorem b1248 : Ban 46 7 v1227 := smallByCut p63_21 w13
theorem b1249 : Ban 46 7 v1228 := smallByCut p63_61 w4
theorem b1250 : Ban 46 7 v1229 := smallByCut p63_42 w13
theorem b1251 : Ban 46 7 v1230 := smallByCut p63_42 w13
theorem b1253 : Ban 46 7 v1231 := smallByCut p63_21 w13
theorem b1254 : Ban 46 7 v1233 := smallByCut p63_21 w13
theorem b1255 : Ban 46 7 v1234 := smallByCut p63_21 w13
theorem b1256 : Ban 46 7 v1235 := smallByCut p63_21 w13
theorem b1257 : Ban 46 7 v1236 := smallByCut p63_55 w4
theorem b1258 : Ban 46 7 v1237 := smallByCut p63_42 w13
theorem b1259 : Ban 46 7 v1238 := smallByCut p63_42 w13
theorem b1260 : Ban 46 7 v1239 := smallByCut p63_42 w13
theorem b1261 : Ban 46 7 v1240 := smallByCut p63_21 w13
theorem b1262 : Ban 46 7 v1241 := smallByCut p63_21 w13
theorem b1264 : Ban 46 7 v1242 := smallByCut p63_42 w13
theorem b1265 : Ban 46 7 v1244 := smallByCut p63_42 w13
theorem b1266 : Ban 46 7 v1245 := smallByCut p63_42 w13
theorem b1267 : Ban 46 7 v1246 := smallByCut p63_42 w13
theorem b1268 : Ban 46 7 v1247 := smallByCut p63_42 w13
theorem b1269 : Ban 46 7 v1248 := smallByCut p63_42 w13
theorem b1271 : Ban 46 7 v1249 := smallByCut p63_42 w13
theorem b1272 : Ban 46 7 v1251 := smallByCut p63_42 w13
theorem b1273 : Ban 46 7 v1252 := smallByCut p63_42 w13
theorem b1274 : Ban 46 7 v1253 := smallByCut p63_42 w13
theorem b1275 : Ban 46 7 v1254 := smallByCut p63_42 w13
theorem b1276 : Ban 46 7 v1255 := smallByCut p63_42 w13
theorem b1277 : Ban 46 7 v1256 := smallByCut p63_42 w13
theorem b1278 : Ban 46 7 v1257 := smallByCut p63_42 w13
theorem b1279 : Ban 46 7 v1258 := smallByCut p63_42 w13
theorem b1280 : Ban 46 7 v1134 := smallByCut p63_47 w3
theorem b1281 : Ban 46 7 v1259 := smallByCut p63_21 w13
theorem b1282 : Ban 46 7 v1260 := smallByCut p63_21 w13
theorem b1283 : Ban 46 7 v1261 := smallByCut p63_21 w13
theorem b1284 : Ban 46 7 v1262 := smallByCut p63_55 w4
theorem b1285 : Ban 46 7 v1263 := smallByCut p63_42 w13
theorem b1286 : Ban 46 7 v1264 := smallByCut p63_42 w13
theorem b1287 : Ban 46 7 v1265 := smallByCut p63_42 w13
theorem b1288 : Ban 46 7 v1266 := smallByCut p63_21 w13
theorem b1290 : Ban 46 7 v1267 := smallByCut p63_42 w13
theorem b1291 : Ban 46 7 v1269 := smallByCut p63_42 w13
theorem b1292 : Ban 46 7 v1270 := smallByCut p63_42 w13
theorem b1289 : Ban 46 7 v1268 := smallByCut p63_42 w13
theorem b1293 : Ban 46 7 v1271 := smallByCut p63_42 w13
theorem b1294 : Ban 46 7 v1272 := smallByCut p63_42 w13
theorem b1295 : Ban 12 4 v1275 := checkedSmall
theorem b1296 : Ban 12 4 v1276 := checkedSmall
theorem b1297 : Ban 12 4 v1277 := checkedSmall
theorem b1298 : Ban 12 4 v1278 := checkedSmall
theorem b1299 : Ban 12 4 v1279 := checkedSmall
theorem b1300 : Ban 12 4 v1280 := checkedSmall
theorem b1301 : Ban 12 4 v1281 := checkedSmall
theorem b1302 : Ban 12 4 v1282 := checkedSmall
theorem b1303 : Ban 12 4 v1283 := checkedSmall
theorem b1304 : Ban 12 4 v1284 := checkedSmall
theorem b1305 : Ban 12 4 v1285 := checkedSmall
theorem b1306 : Ban 12 4 v1286 := checkedSmall
theorem b1307 : Ban 12 3 v1289 := checkedSmall
theorem b1308 : Ban 12 3 v1290 := checkedSmall
theorem b1309 : Ban 12 3 v1291 := checkedSmall
theorem b1310 : Ban 12 3 v1292 := checkedSmall
theorem b1311 : Ban 12 3 v1293 := checkedSmall
theorem b1312 : Ban 12 3 v1294 := checkedSmall
theorem b1313 : Ban 12 3 v1295 := checkedSmall
theorem b1314 : Ban 12 3 v1296 := checkedSmall
theorem b1315 : Ban 12 3 v1297 := checkedSmall
theorem b1316 : Ban 12 3 v1298 := checkedSmall
theorem b1317 : Ban 12 3 v1299 := checkedSmall
theorem b1318 : Ban 12 3 v1300 := checkedSmall
theorem b1319 : Ban 12 3 v1301 := checkedSmall
theorem b1320 : Ban 12 3 v1302 := checkedSmall
theorem b1321 : Ban 12 3 v1303 := checkedSmall
theorem b1322 : Ban 12 3 v1304 := checkedSmall
theorem b1323 : Ban 12 3 v1305 := checkedSmall
theorem b1324 : Ban 12 3 v1306 := checkedSmall
theorem b1325 : Ban 12 3 v1307 := checkedSmall
theorem b1326 : Ban 12 3 v1308 := checkedSmall
theorem b1327 : Ban 12 3 v1274 := checkedSmall
theorem b1328 : Ban 12 3 v1287 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1329 : Ban 12 4 v1288 := viaBranch (ws := [v1289,v1290,v1291,v1292,v1293,v1294,v1295,v1296,v1297,v1298,v1299,v1300,v1301,v1302,v1303,v1304,v1305,v1306,v1307,v1308,v1274,v1287]) (consBan b1307 (consBan b1308 (consBan b1309 (consBan b1310 (consBan b1311 (consBan b1312 (consBan b1313 (consBan b1314 (consBan b1315 (consBan b1316 (consBan b1317 (consBan b1318 (consBan b1319 (consBan b1320 (consBan b1321 (consBan b1322 (consBan b1323 (consBan b1324 (consBan b1325 (consBan b1326 (consBan b1327 (consBan b1328 (nilBan 12 3))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1330 : Ban 12 4 v1287 := viaPerm map39_1 map39_1 b1329 (by decide +kernel) (by decide +kernel)
theorem b1331 : Ban 12 4 v1309 := checkedSmall
theorem b1332 : Ban 12 4 v1310 := checkedSmall
theorem b1333 : Ban 12 4 v1311 := checkedSmall
theorem b1334 : Ban 12 4 v1312 := checkedSmall
theorem b1335 : Ban 12 4 v1313 := checkedSmall
theorem b1336 : Ban 12 4 v1314 := checkedSmall
theorem b1337 : Ban 12 4 v1315 := checkedSmall
theorem b1338 : Ban 12 4 v1316 := checkedSmall
theorem b1339 : Ban 12 4 v1317 := checkedSmall
theorem b1340 : Ban 12 4 v1318 := checkedSmall
theorem b1341 : Ban 12 4 v1319 := checkedSmall
theorem b1342 : Ban 12 4 v1320 := checkedSmall
theorem b1343 : Ban 12 4 v1321 := checkedSmall
theorem b1344 : Ban 12 4 v1322 := checkedSmall
theorem b1345 : Ban 12 4 v1323 := checkedSmall
theorem b1346 : Ban 12 4 v1324 := checkedSmall
theorem b1347 : Ban 12 4 v1325 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1348 : Ban 12 5 v1274 := viaBranch (ws := [v1275,v1276,v1277,v1278,v1279,v1280,v1281,v1282,v1283,v1284,v1285,v1286,v1072,v1287,v1288,v1309,v1310,v1311,v1312,v1313,v1314,v1315,v1316,v1317,v1318,v1319,v1320,v1321,v1322,v1323,v1324,v1325]) (consBan b1295 (consBan b1296 (consBan b1297 (consBan b1298 (consBan b1299 (consBan b1300 (consBan b1301 (consBan b1302 (consBan b1303 (consBan b1304 (consBan b1305 (consBan b1306 (consBan b1089 (consBan b1330 (consBan b1329 (consBan b1331 (consBan b1332 (consBan b1333 (consBan b1334 (consBan b1335 (consBan b1336 (consBan b1337 (consBan b1338 (consBan b1339 (consBan b1340 (consBan b1341 (consBan b1342 (consBan b1343 (consBan b1344 (consBan b1345 (consBan b1346 (consBan b1347 (nilBan 12 4))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w15 : Wide 12 5 v1274 := viaSub (ws := [v1274]) (consBan b1348 (nilBan 12 5)) (by decide) (by decide +kernel)
theorem b1349 : Ban 46 7 v1273 := smallByCut p63_39 w15
theorem b1350 : Ban 46 7 v1326 := smallByCut p63_42 w13
theorem b1351 : Ban 46 7 v1327 := smallByCut p63_21 w13
theorem b1352 : Ban 46 7 v1328 := smallByCut p63_21 w13
theorem b1353 : Ban 46 7 v1329 := smallByCut p63_21 w13
theorem b1354 : Ban 46 7 v1330 := smallByCut p63_21 w13
theorem b1355 : Ban 46 7 v1331 := smallByCut p63_21 w13
theorem b1356 : Ban 46 7 v1332 := smallByCut p63_21 w13
theorem b1357 : Ban 46 7 v1333 := smallByCut p63_21 w13
theorem b1358 : Ban 46 7 v1334 := smallByCut p63_42 w13
theorem b1359 : Ban 46 7 v1335 := smallByCut p63_21 w13
theorem b1360 : Ban 46 7 v1336 := smallByCut p63_42 w13
theorem b1361 : Ban 46 7 v1337 := smallByCut p63_21 w13
theorem b1362 : Ban 46 7 v1338 := smallByCut p63_42 w13
theorem b1363 : Ban 46 7 v1339 := smallByCut p63_21 w13
theorem b1364 : Ban 46 7 v1340 := smallByCut p63_42 w13
theorem b1365 : Ban 46 7 v1341 := smallByCut p63_21 w13
theorem b1366 : Ban 46 7 v1342 := smallByCut p63_21 w13
theorem b1367 : Ban 46 7 v1343 := smallByCut p63_21 w13
theorem b1368 : Ban 46 7 v1344 := smallByCut p63_21 w13
theorem b1369 : Ban 46 7 v1345 := smallByCut p63_21 w13
theorem b1370 : Ban 46 7 v1346 := smallByCut p63_42 w13
theorem b1371 : Ban 46 7 v1347 := smallByCut p63_21 w13
theorem b1372 : Ban 46 7 v1348 := smallByCut p63_42 w13
theorem b1373 : Ban 46 7 v1349 := smallByCut p63_21 w13
theorem b1374 : Ban 46 7 v1350 := smallByCut p63_42 w13
theorem b1375 : Ban 46 7 v1351 := smallByCut p63_21 w13
theorem b1376 : Ban 46 7 v1352 := smallByCut p63_42 w13
theorem b1377 : Ban 46 7 v1353 := smallByCut p63_21 w13
theorem b1378 : Ban 46 7 v1354 := smallByCut p63_21 w13
theorem b1379 : Ban 46 7 v1355 := smallByCut p63_21 w13
theorem b1380 : Ban 46 7 v1356 := smallByCut p63_21 w13
theorem b1382 : Ban 46 7 v1357 := smallByCut p63_42 w13
theorem b1383 : Ban 46 7 v1359 := smallByCut p63_42 w13
theorem b1384 : Ban 46 7 v1360 := smallByCut p63_42 w13
theorem b1385 : Ban 46 7 v1361 := smallByCut p63_42 w13
theorem b1386 : Ban 46 7 v1362 := smallByCut p63_21 w13
theorem b1387 : Ban 46 7 v1363 := smallByCut p63_42 w13
theorem b1388 : Ban 46 7 v1364 := smallByCut p63_42 w13
theorem b1389 : Ban 46 7 v1365 := smallByCut p63_21 w13
theorem b1390 : Ban 46 7 v1366 := smallByCut p63_21 w13
theorem b1391 : Ban 46 7 v1367 := smallByCut p63_42 w13
theorem b1392 : Ban 46 7 v1368 := smallByCut p63_42 w13
theorem b1393 : Ban 46 7 v1369 := smallByCut p63_21 w13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1394 : Ban 46 8 v937 := viaBranch (ws := [v936,v935,v938,v1226,v1227,v1228,v1229,v553,v1230,v1231,v1233,v1234,v1235,v1236,v1237,v1238,v1239,v1240,v1241,v1242,v1244,v1245,v1246,v1247,v1248,v1249,v1251,v1252,v1253,v1254,v1255,v416,v1256,v1257,v1258,v1149,v1134,v1150,v1259,v165,v196,v579,v580,v1260,v1261,v1262,v1263,v1264,v1265,v1266,v1267,v663,v1269,v1270,v1268,v1271,v887,v1272,v1273,v1326,v1327,v1328,v1329,v1330,v1331,v1332,v1333,v1334,v1335,v1336,v1337,v1338,v1339,v1340,v1341,v1342,v1343,v1344,v1345,v1346,v1347,v1348,v1349,v1350,v1351,v1352,v1353,v1354,v1355,v1356,v1357,v1359,v1360,v1361,v1362,v1363,v1364,v1365,v1366,v1367,v1368,v1369]) (consBan b953 (consBan b1246 (consBan b955 (consBan b1247 (consBan b1248 (consBan b1249 (consBan b1250 (consBan b558 (consBan b1251 (consBan b1253 (consBan b1254 (consBan b1255 (consBan b1256 (consBan b1257 (consBan b1258 (consBan b1259 (consBan b1260 (consBan b1261 (consBan b1262 (consBan b1264 (consBan b1265 (consBan b1266 (consBan b1267 (consBan b1268 (consBan b1269 (consBan b1271 (consBan b1272 (consBan b1273 (consBan b1274 (consBan b1275 (consBan b1276 (consBan b416 (consBan b1277 (consBan b1278 (consBan b1279 (consBan b1168 (consBan b1280 (consBan b1169 (consBan b1281 (consBan b195 (consBan b196 (consBan b584 (consBan b585 (consBan b1282 (consBan b1283 (consBan b1284 (consBan b1285 (consBan b1286 (consBan b1287 (consBan b1288 (consBan b1290 (consBan b670 (consBan b1291 (consBan b1292 (consBan b1289 (consBan b1293 (consBan b900 (consBan b1294 (consBan b1349 (consBan b1350 (consBan b1351 (consBan b1352 (consBan b1353 (consBan b1354 (consBan b1355 (consBan b1356 (consBan b1357 (consBan b1358 (consBan b1359 (consBan b1360 (consBan b1361 (consBan b1362 (consBan b1363 (consBan b1364 (consBan b1365 (consBan b1366 (consBan b1367 (consBan b1368 (consBan b1369 (consBan b1370 (consBan b1371 (consBan b1372 (consBan b1373 (consBan b1374 (consBan b1375 (consBan b1376 (consBan b1377 (consBan b1378 (consBan b1379 (consBan b1380 (consBan b1382 (consBan b1383 (consBan b1384 (consBan b1385 (consBan b1386 (consBan b1387 (consBan b1388 (consBan b1389 (consBan b1390 (consBan b1391 (consBan b1392 (consBan b1393 (nilBan 46 7))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1395 : Ban 46 8 v1043 := viaPerm map63_4 map63_4 b1394 (by decide +kernel) (by decide +kernel)
theorem b1396 : Ban 46 8 v1370 := smallByCut p63_55 w12
theorem b1397 : Ban 46 7 v1373 := smallByCut p63_42 w13
theorem b1398 : Ban 46 7 v1374 := smallByCut p63_42 w13
theorem b1399 : Ban 46 7 v1375 := smallByCut p63_42 w13
theorem b1400 : Ban 46 7 v1376 := smallByCut p63_42 w13
theorem b1401 : Ban 46 7 v1377 := smallByCut p63_42 w13
theorem b1402 : Ban 46 7 v1378 := smallByCut p63_42 w13
theorem b1403 : Ban 46 7 v1379 := smallByCut p63_42 w13
theorem b1404 : Ban 46 7 v1380 := smallByCut p63_42 w13
theorem b1406 : Ban 46 7 v1381 := smallByCut p63_42 w13
theorem b1407 : Ban 46 7 v1383 := smallByCut p63_42 w13
theorem b1408 : Ban 46 7 v1384 := smallByCut p63_42 w13
theorem b731 : Ban 46 7 v724 := smallByCut p63_42 w13
theorem b1409 : Ban 46 7 v1385 := smallByCut p63_42 w13
theorem b1410 : Ban 46 7 v1386 := smallByCut p63_42 w13
theorem b1411 : Ban 46 7 v1387 := smallByCut p63_42 w13
theorem b1412 : Ban 46 7 v1388 := smallByCut p63_42 w13
theorem b1413 : Ban 46 7 v1389 := smallByCut p63_42 w13
theorem b1414 : Ban 46 7 v1390 := smallByCut p63_42 w13
theorem b1415 : Ban 46 7 v1391 := smallByCut p63_42 w13
theorem b1416 : Ban 46 7 v1392 := smallByCut p63_42 w13
theorem b1417 : Ban 46 7 v1393 := smallByCut p63_42 w13
theorem b1418 : Ban 46 7 v1394 := smallByCut p63_42 w13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w16 : Wide 25 5 v9 := viaSub (ws := [v3,v9]) (consBan b672 (consBan b5 (nilBan 25 5))) (by decide) (by decide +kernel)
theorem b1419 : Ban 46 7 v1395 := smallByCut p63_55 w16
theorem b1420 : Ban 46 7 v1396 := checkedSmall
theorem b1421 : Ban 46 7 v1397 := smallByCut p63_61 w16
theorem b1422 : Ban 46 7 v1398 := smallByCut p63_55 w16
theorem b1423 : Ban 46 7 v1399 := smallByCut p63_42 w13
theorem b1424 : Ban 46 7 v1400 := smallByCut p63_42 w13
theorem b1425 : Ban 46 7 v1401 := smallByCut p63_42 w13
theorem b1426 : Ban 46 7 v1402 := smallByCut p63_42 w13
theorem b1427 : Ban 46 7 v1403 := smallByCut p63_42 w13
theorem b1428 : Ban 46 7 v1404 := smallByCut p63_42 w13
theorem b1429 : Ban 46 7 v1405 := smallByCut p63_42 w13
theorem b1430 : Ban 46 7 v1406 := smallByCut p63_42 w13
theorem b1431 : Ban 46 7 v1407 := smallByCut p63_21 w13
theorem b1432 : Ban 46 7 v1408 := smallByCut p63_42 w13
theorem b1433 : Ban 46 7 v1409 := checkedSmall
theorem b1434 : Ban 46 7 v1410 := smallByCut p63_42 w13
theorem b1435 : Ban 46 7 v1411 := smallByCut p63_21 w13
theorem b1436 : Ban 46 7 v1412 := smallByCut p63_42 w13
theorem b1437 : Ban 46 7 v1413 := smallByCut p63_42 w13
theorem b1438 : Ban 46 7 v1414 := smallByCut p63_42 w13
theorem b1440 : Ban 46 7 v1415 := smallByCut p63_61 w16
theorem b1441 : Ban 46 7 v1417 := checkedSmall
theorem b1442 : Ban 46 7 v1418 := smallByCut p63_61 w16
theorem b1443 : Ban 46 7 v1419 := checkedSmall
theorem b1444 : Ban 46 7 v1420 := smallByCut p63_42 w13
theorem b1445 : Ban 46 7 v1421 := smallByCut p63_42 w13
theorem b1446 : Ban 46 7 v1422 := smallByCut p63_42 w13
theorem b1447 : Ban 46 7 v1423 := smallByCut p63_42 w13
theorem b1448 : Ban 46 7 v1424 := smallByCut p63_42 w13
theorem b1449 : Ban 46 7 v1425 := smallByCut p63_42 w13
theorem b1450 : Ban 46 7 v1426 := smallByCut p63_42 w13
theorem b1451 : Ban 46 7 v1427 := smallByCut p63_42 w13
theorem b1452 : Ban 46 7 v1428 := smallByCut p63_21 w13
theorem b1453 : Ban 46 7 v1429 := smallByCut p63_42 w13
theorem b1454 : Ban 46 7 v1430 := checkedSmall
theorem b1455 : Ban 46 7 v1431 := smallByCut p63_42 w13
theorem b1456 : Ban 46 7 v1432 := smallByCut p63_21 w13
theorem b1457 : Ban 46 7 v1433 := smallByCut p63_42 w13
theorem b1458 : Ban 46 7 v1434 := smallByCut p63_42 w13
theorem b1459 : Ban 46 7 v1435 := smallByCut p63_42 w13
theorem b1460 : Ban 46 7 v1436 := smallByCut p63_55 w16
theorem b1461 : Ban 46 7 v1437 := checkedSmall
theorem b1462 : Ban 46 7 v1438 := smallByCut p63_55 w16
theorem b1463 : Ban 46 7 v1439 := smallByCut p63_42 w13
theorem b1465 : Ban 46 7 v1440 := smallByCut p63_47 w12
theorem b1467 : Ban 46 7 v1442 := smallByCut p63_42 w13
theorem b1468 : Ban 46 7 v1444 := smallByCut p63_42 w13
theorem b1469 : Ban 46 7 v1445 := smallByCut p63_42 w13
theorem b1471 : Ban 46 7 v1446 := smallByCut p63_42 w13
theorem b1472 : Ban 46 7 v1448 := smallByCut p63_42 w13
theorem b1473 : Ban 46 7 v1449 := smallByCut p63_42 w13
theorem b1474 : Ban 46 7 v1450 := smallByCut p63_42 w13
theorem b1476 : Ban 46 7 v1451 := smallByCut p63_42 w13
theorem b1477 : Ban 46 7 v1453 := smallByCut p63_42 w13
theorem b1478 : Ban 46 7 v1454 := smallByCut p63_42 w13
theorem b1479 : Ban 46 7 v1455 := smallByCut p63_42 w13
theorem b1480 : Ban 46 7 v1456 := smallByCut p63_42 w13
theorem b1481 : Ban 46 7 v1457 := smallByCut p63_42 w13
theorem b1482 : Ban 46 7 v1458 := smallByCut p63_42 w13
theorem b1483 : Ban 46 7 v1459 := smallByCut p63_42 w13
theorem b1484 : Ban 46 7 v1460 := smallByCut p63_42 w13
theorem b1485 : Ban 46 7 v1461 := smallByCut p63_42 w13
theorem b1486 : Ban 46 7 v1462 := smallByCut p63_21 w13
theorem b1487 : Ban 46 7 v1463 := smallByCut p63_42 w13
theorem b1488 : Ban 46 7 v1464 := smallByCut p63_42 w13
theorem b1490 : Ban 46 7 v334 := smallByCut p63_42 w13
theorem b1491 : Ban 46 7 v1466 := smallByCut p63_42 w13
theorem b1492 : Ban 46 7 v1467 := smallByCut p63_21 w13
theorem b1493 : Ban 46 7 v1468 := smallByCut p63_42 w13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1494 : Ban 46 8 v1372 := viaBranch (ws := [v1373,v435,v614,v1374,v1375,v1376,v1377,v1378,v1379,v723,v725,v1380,v1381,v1383,v1384,v724,v1385,v923,v1386,v1387,v1388,v1389,v745,v1390,v859,v1391,v1392,v1393,v1097,v1199,v1359,v1394,v1395,v1396,v1397,v1398,v1399,v1400,v1401,v1402,v1403,v1404,v1405,v1406,v1407,v1408,v1409,v1410,v1411,v1412,v1413,v1414,v1415,v1417,v1418,v1419,v1420,v1421,v1422,v1423,v1424,v1425,v1426,v1427,v1428,v1429,v1430,v1431,v1432,v1433,v1434,v1435,v1436,v1437,v1438,v1439,v1440,v1442,v1444,v1445,v1446,v1448,v1449,v1450,v1451,v1453,v1454,v1455,v1456,v1457,v1458,v1459,v1460,v1461,v1462,v1463,v302,v1464,v334,v1466,v1467,v1468]) (consBan b1397 (consBan b436 (consBan b619 (consBan b1398 (consBan b1399 (consBan b1400 (consBan b1401 (consBan b1402 (consBan b1403 (consBan b732 (consBan b733 (consBan b1404 (consBan b1406 (consBan b1407 (consBan b1408 (consBan b731 (consBan b1409 (consBan b936 (consBan b1410 (consBan b1411 (consBan b1412 (consBan b1413 (consBan b753 (consBan b1414 (consBan b871 (consBan b1415 (consBan b1416 (consBan b1417 (consBan b1115 (consBan b1218 (consBan b1383 (consBan b1418 (consBan b1419 (consBan b1420 (consBan b1421 (consBan b1422 (consBan b1423 (consBan b1424 (consBan b1425 (consBan b1426 (consBan b1427 (consBan b1428 (consBan b1429 (consBan b1430 (consBan b1431 (consBan b1432 (consBan b1433 (consBan b1434 (consBan b1435 (consBan b1436 (consBan b1437 (consBan b1438 (consBan b1440 (consBan b1441 (consBan b1442 (consBan b1443 (consBan b1444 (consBan b1445 (consBan b1446 (consBan b1447 (consBan b1448 (consBan b1449 (consBan b1450 (consBan b1451 (consBan b1452 (consBan b1453 (consBan b1454 (consBan b1455 (consBan b1456 (consBan b1457 (consBan b1458 (consBan b1459 (consBan b1460 (consBan b1461 (consBan b1462 (consBan b1463 (consBan b1465 (consBan b1467 (consBan b1468 (consBan b1469 (consBan b1471 (consBan b1472 (consBan b1473 (consBan b1474 (consBan b1476 (consBan b1477 (consBan b1478 (consBan b1479 (consBan b1480 (consBan b1481 (consBan b1482 (consBan b1483 (consBan b1484 (consBan b1485 (consBan b1486 (consBan b1487 (consBan b334 (consBan b1488 (consBan b1490 (consBan b1491 (consBan b1492 (consBan b1493 (nilBan 46 7))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1495 : Ban 46 8 v1371 := viaPerm map63_4 map63_4 b1494 (by decide +kernel) (by decide +kernel)
theorem b1496 : Ban 46 8 v1452 := smallByCut p63_61 w12
theorem b1497 : Ban 46 8 v1469 := smallByCut p63_55 w12
theorem b1499 : Ban 46 8 v1470 := smallByCut p63_59 w12
theorem b1500 : Ban 46 7 v1473 := smallByCut p63_21 w13
theorem b1501 : Ban 46 7 v1474 := smallByCut p63_61 w12
theorem b1502 : Ban 46 7 v1475 := smallByCut p63_21 w13
theorem b1503 : Ban 46 7 v1476 := smallByCut p63_21 w13
theorem b1504 : Ban 46 7 v1477 := checkedSmall
theorem b1505 : Ban 46 7 v1478 := smallByCut p63_42 w13
theorem b1506 : Ban 46 7 v1479 := smallByCut p63_21 w13
theorem b1507 : Ban 46 7 v1480 := smallByCut p63_42 w13
theorem b1508 : Ban 46 7 v1481 := smallByCut p63_42 w13
theorem b1509 : Ban 46 7 v1482 := smallByCut p63_42 w13
theorem b1511 : Ban 46 7 v1483 := smallByCut p63_42 w13
theorem b1512 : Ban 46 7 v1485 := smallByCut p63_42 w13
theorem b1513 : Ban 46 7 v1486 := checkedSmall
theorem b1514 : Ban 46 7 v1487 := smallByCut p63_42 w13
theorem b1515 : Ban 46 7 v1488 := checkedSmall
theorem b1516 : Ban 46 7 v1489 := checkedSmall
theorem b1517 : Ban 46 7 v1490 := smallByCut p63_42 w13
theorem b1518 : Ban 46 7 v1491 := smallByCut p63_42 w13
theorem b1519 : Ban 46 7 v1492 := smallByCut p63_42 w13
theorem b1520 : Ban 46 7 v1493 := smallByCut p63_21 w13
theorem b1521 : Ban 46 7 v1494 := smallByCut p63_21 w13
theorem b1522 : Ban 46 7 v1495 := smallByCut p63_21 w13
theorem b1523 : Ban 46 7 v1496 := smallByCut p63_21 w13
theorem b1524 : Ban 46 7 v1497 := smallByCut p63_21 w13
theorem b1526 : Ban 46 7 v1498 := smallByCut p63_59 w12
theorem b1528 : Ban 46 7 v1500 := smallByCut p63_21 w13
theorem b1529 : Ban 46 7 v1502 := smallByCut p63_42 w13
theorem b1530 : Ban 46 7 v1503 := smallByCut p63_21 w13
theorem b1531 : Ban 46 7 v1504 := smallByCut p63_21 w13
theorem b1532 : Ban 46 7 v1505 := smallByCut p63_21 w13
theorem b1533 : Ban 46 7 v1506 := smallByCut p63_42 w13
theorem b1534 : Ban 46 7 v1507 := smallByCut p63_42 w13
theorem b1535 : Ban 46 7 v1508 := smallByCut p63_42 w13
theorem b1536 : Ban 46 7 v1509 := smallByCut p63_21 w13
theorem solidb111 : Wide 26 6 v67 := solid b111
theorem b1539 : Ban 46 7 v1510 := smallByCut p63_62 solidb111
theorem b1540 : Ban 46 7 v1513 := smallByCut p63_61 w12
theorem b1541 : Ban 46 7 v1514 := smallByCut p63_61 w12
theorem b1542 : Ban 46 7 v1515 := smallByCut p63_21 w13
theorem b1543 : Ban 46 7 v1516 := smallByCut p63_42 w13
theorem b1544 : Ban 46 7 v1517 := smallByCut p63_21 w13
theorem b1545 : Ban 46 7 v1518 := smallByCut p63_21 w13
theorem b1546 : Ban 46 7 v1519 := smallByCut p63_21 w13
theorem b1547 : Ban 46 7 v1520 := smallByCut p63_21 w13
theorem b1548 : Ban 46 7 v1521 := smallByCut p63_21 w13
theorem b1549 : Ban 46 7 v1522 := smallByCut p63_31 solidb111
theorem b1550 : Ban 46 7 v1523 := smallByCut p63_59 w12
theorem b1551 : Ban 46 7 v1524 := smallByCut p63_21 w13
theorem b1552 : Ban 46 7 v1525 := smallByCut p63_59 w12
theorem b1553 : Ban 46 7 v1526 := smallByCut p63_42 w13
theorem b1554 : Ban 46 7 v1527 := smallByCut p63_21 w13
theorem b1555 : Ban 46 7 v1528 := smallByCut p63_21 w13
theorem b1556 : Ban 46 7 v1529 := checkedSmall
theorem b1557 : Ban 46 7 v1530 := checkedSmall
theorem b1558 : Ban 46 7 v1531 := smallByCut p63_21 w13
theorem b1559 : Ban 46 7 v1532 := smallByCut p63_21 w13
theorem b1560 : Ban 46 7 v1533 := checkedSmall
theorem b1561 : Ban 46 7 v1534 := checkedSmall
theorem b1562 : Ban 46 7 v1535 := smallByCut p63_21 w13
theorem b1563 : Ban 46 7 v1536 := checkedSmall
theorem b1564 : Ban 46 7 v1537 := smallByCut p63_21 w13
theorem b1565 : Ban 46 7 v1538 := smallByCut p63_42 w13
theorem b1566 : Ban 46 7 v1539 := smallByCut p63_21 w13
theorem b1567 : Ban 46 7 v1540 := smallByCut p63_21 w13
theorem b1568 : Ban 46 7 v1541 := smallByCut p63_21 w13
theorem b1569 : Ban 46 7 v1542 := smallByCut p63_21 w13
theorem b1570 : Ban 46 7 v1543 := smallByCut p63_21 w13
theorem b1571 : Ban 46 7 v1544 := smallByCut p63_42 w13
theorem b1572 : Ban 46 7 v1545 := smallByCut p63_42 w13
theorem b1573 : Ban 46 7 v1546 := smallByCut p63_42 w13
theorem b1574 : Ban 46 7 v1547 := smallByCut p63_21 w13
theorem b1575 : Ban 46 7 v1548 := viaPerm map63_1 map63_1 b243 (by decide +kernel) (by decide +kernel)
theorem b1576 : Ban 46 7 v1549 := smallByCut p63_59 w12
theorem b1577 : Ban 46 7 v1550 := smallByCut p63_59 w12
theorem b1578 : Ban 46 7 v1551 := smallByCut p63_42 w13
theorem b1579 : Ban 46 7 v1552 := smallByCut p63_21 w13
theorem b1580 : Ban 46 7 v1553 := smallByCut p63_42 w13
theorem b1581 : Ban 46 7 v1554 := smallByCut p63_42 w13
theorem b1582 : Ban 46 7 v1555 := checkedSmall
theorem b1583 : Ban 46 7 v1556 := checkedSmall
theorem b1584 : Ban 46 7 v1557 := checkedSmall
theorem b1585 : Ban 46 7 v1558 := smallByCut p63_42 w13
theorem b1586 : Ban 46 7 v1559 := smallByCut p63_42 w13
theorem b1510 : Ban 46 7 v1484 := smallByCut p63_21 w13
theorem b1587 : Ban 46 7 v1560 := smallByCut p63_21 w13
theorem b1588 : Ban 46 7 v1561 := checkedSmall
theorem b1589 : Ban 46 7 v1562 := checkedSmall
theorem b1590 : Ban 46 7 v1563 := checkedSmall
theorem b1591 : Ban 46 7 v1564 := checkedSmall
theorem b1592 : Ban 46 7 v1565 := smallByCut p63_21 w13
theorem b1593 : Ban 46 7 v1566 := smallByCut p63_21 w13
theorem b1594 : Ban 46 7 v1567 := smallByCut p63_21 w13
theorem b1595 : Ban 46 7 v1568 := checkedSmall
theorem b1596 : Ban 46 7 v1569 := smallByCut p63_42 w13
theorem b1597 : Ban 46 7 v1570 := smallByCut p63_21 w13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1598 : Ban 46 8 v1472 := viaBranch (ws := [v1473,v208,v245,v587,v1474,v1475,v1476,v1477,v1478,v1479,v1480,v670,v1481,v1482,v1483,v1485,v362,v1486,v533,v1487,v1488,v1489,v1490,v1491,v895,v1492,v1101,v1158,v1334,v1493,v1494,v1495,v1496,v1497,v1498,v1500,v1502,v1503,v1504,v1505,v1506,v1507,v1508,v1509,v1510,v1513,v1514,v1515,v1516,v1517,v1518,v1519,v1520,v1521,v1522,v1523,v1524,v1525,v1526,v1527,v1528,v1529,v1530,v1531,v1532,v1533,v1534,v1535,v1536,v1537,v1538,v1539,v1540,v1541,v1542,v1543,v1544,v1400,v1545,v1546,v1547,v1548,v1549,v1550,v1551,v1552,v1553,v1554,v1409,v1555,v1556,v1557,v1558,v1559,v1484,v1560,v1561,v1562,v1563,v1564,v1565,v1566,v1567,v1568,v1569,v1570]) (consBan b1500 (consBan b244 (consBan b245 (consBan b592 (consBan b1501 (consBan b1502 (consBan b1503 (consBan b1504 (consBan b1505 (consBan b1506 (consBan b1507 (consBan b678 (consBan b1508 (consBan b1509 (consBan b1511 (consBan b1512 (consBan b363 (consBan b1513 (consBan b538 (consBan b1514 (consBan b1515 (consBan b1516 (consBan b1517 (consBan b1518 (consBan b908 (consBan b1519 (consBan b1120 (consBan b1177 (consBan b1358 (consBan b1520 (consBan b1521 (consBan b1522 (consBan b1523 (consBan b1524 (consBan b1526 (consBan b1528 (consBan b1529 (consBan b1530 (consBan b1531 (consBan b1532 (consBan b1533 (consBan b1534 (consBan b1535 (consBan b1536 (consBan b1539 (consBan b1540 (consBan b1541 (consBan b1542 (consBan b1543 (consBan b1544 (consBan b1545 (consBan b1546 (consBan b1547 (consBan b1548 (consBan b1549 (consBan b1550 (consBan b1551 (consBan b1552 (consBan b1553 (consBan b1554 (consBan b1555 (consBan b1556 (consBan b1557 (consBan b1558 (consBan b1559 (consBan b1560 (consBan b1561 (consBan b1562 (consBan b1563 (consBan b1564 (consBan b1565 (consBan b1566 (consBan b1567 (consBan b1568 (consBan b1569 (consBan b1570 (consBan b1571 (consBan b1424 (consBan b1572 (consBan b1573 (consBan b1574 (consBan b1575 (consBan b1576 (consBan b1577 (consBan b1578 (consBan b1579 (consBan b1580 (consBan b1581 (consBan b1433 (consBan b1582 (consBan b1583 (consBan b1584 (consBan b1585 (consBan b1586 (consBan b1510 (consBan b1587 (consBan b1588 (consBan b1589 (consBan b1590 (consBan b1591 (consBan b1592 (consBan b1593 (consBan b1594 (consBan b1595 (consBan b1596 (consBan b1597 (nilBan 46 7))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1600 : Ban 46 8 v1543 := smallByCut p63_61 w12
theorem b1601 : Ban 46 8 v1508 := smallByCut p63_59 w12
theorem b1602 : Ban 46 8 v1572 := smallByCut p63_47 w12
theorem b1603 : Ban 46 8 v1573 := viaPerm map63_1 map63_1 b1598 (by decide +kernel) (by decide +kernel)
theorem b1604 : Ban 46 8 v1574 := smallByCut p63_61 w12
theorem b1605 : Ban 46 8 v1575 := smallByCut p63_47 w12
theorem b1606 : Ban 46 8 v1576 := smallByCut p63_61 w12
theorem b1607 : Ban 46 8 v1577 := viaPerm map63_4 map63_4 b822 (by decide +kernel) (by decide +kernel)
theorem b949 : Ban 46 8 v653 := smallByCut p63_61 w12
theorem b1608 : Ban 46 8 v1578 := viaPerm map63_5 map63_6 b947 (by decide +kernel) (by decide +kernel)
theorem b1498 : Ban 46 8 v1471 := smallByCut p63_55 w12
theorem b1609 : Ban 46 8 v1579 := viaPerm map63_2 map63_2 b1598 (by decide +kernel) (by decide +kernel)
theorem b1610 : Ban 46 8 v1580 := smallByCut p63_55 w12
theorem b1611 : Ban 46 8 v1581 := smallByCut p63_59 w12
theorem b1612 : Ban 46 8 v1582 := smallByCut p63_47 w12
theorem b1613 : Ban 46 8 v1583 := viaPerm map63_3 map63_3 b1598 (by decide +kernel) (by decide +kernel)
theorem b1599 : Ban 46 8 v1571 := smallByCut p63_55 w12
theorem b1614 : Ban 46 8 v1584 := smallByCut p63_47 w12
theorem b1615 : Ban 46 8 v1585 := smallByCut p63_55 w12
theorem b1616 : Ban 46 8 v1586 := viaPerm map63_5 map63_6 b822 (by decide +kernel) (by decide +kernel)
theorem b1617 : Ban 46 8 v1587 := smallByCut p63_55 w12
theorem b1618 : Ban 46 8 v1588 := viaPerm map63_4 map63_4 b947 (by decide +kernel) (by decide +kernel)
theorem b1619 : Ban 46 8 v1589 := smallByCut p63_47 w12
theorem b1620 : Ban 46 8 v1457 := smallByCut p63_59 w12
theorem b1621 : Ban 46 8 v1451 := smallByCut p63_47 w12
theorem b45 : Ban 46 8 v2 := smallByCut p63_59 w12
theorem b1622 : Ban 46 8 v1590 := viaPerm map63_4 map63_4 b447 (by decide +kernel) (by decide +kernel)
theorem b631 : Ban 46 8 v62 := smallByCut p63_59 w12
theorem b1623 : Ban 46 8 v1591 := viaPerm map63_4 map63_4 b630 (by decide +kernel) (by decide +kernel)
theorem b1624 : Ban 46 8 v1592 := smallByCut p63_47 w12
theorem b1625 : Ban 46 8 v1593 := viaPerm map63_6 map63_5 b447 (by decide +kernel) (by decide +kernel)
theorem b1626 : Ban 46 8 v1594 := smallByCut p63_47 w12
theorem b1627 : Ban 46 8 v1595 := viaPerm map63_6 map63_5 b630 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1628 : Ban 46 9 v0 := viaBranch (ws := [v1,v48,v198,v61,v625,v626,v627,v628,v629,v631,v719,v652,v630,v862,v720,v934,v935,v1134,v937,v1043,v1370,v1371,v1452,v1469,v1470,v1472,v1543,v1508,v1572,v1573,v1574,v1575,v1576,v1577,v653,v1578,v1471,v1579,v1580,v1581,v1582,v1583,v1571,v1584,v1585,v1586,v1587,v1588,v1589,v1372,v1457,v1451,v2,v1590,v62,v1591,v1592,v1593,v1594,v1595]) (consBan b46 (consBan b447 (consBan b630 (consBan b632 (consBan b633 (consBan b634 (consBan b635 (consBan b636 (consBan b638 (consBan b822 (consBan b948 (consBan b950 (consBan b637 (consBan b951 (consBan b947 (consBan b952 (consBan b1153 (consBan b1245 (consBan b1394 (consBan b1395 (consBan b1396 (consBan b1495 (consBan b1496 (consBan b1497 (consBan b1499 (consBan b1598 (consBan b1600 (consBan b1601 (consBan b1602 (consBan b1603 (consBan b1604 (consBan b1605 (consBan b1606 (consBan b1607 (consBan b949 (consBan b1608 (consBan b1498 (consBan b1609 (consBan b1610 (consBan b1611 (consBan b1612 (consBan b1613 (consBan b1599 (consBan b1614 (consBan b1615 (consBan b1616 (consBan b1617 (consBan b1618 (consBan b1619 (consBan b1494 (consBan b1620 (consBan b1621 (consBan b45 (consBan b1622 (consBan b631 (consBan b1623 (consBan b1624 (consBan b1625 (consBan b1626 (consBan b1627 (nilBan 46 8))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem verifiedPin : Wide 46 9 v0 := widen (by decide +kernel) b1628
end PEqualNP.Outside.L_meta_14776.Support

namespace PEqualNP.Outside.L_meta_14776.Data
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_14776.Support
def target (x : Fin 8 → Bool) := decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def posBits : ℕ := 0x909e0e0d0d0c4c4c2b0b0a2a0a094949286848482827070646462625454505046464242343432322626242416161212
def negBits : ℕ := 0x108c060c090c044c0903022802090149006800480026030604460224414401044064002301430222206200414061002
def sample (bank : ℕ) (i : Fin 48) (j : Fin 8) := bank.testBit (8*i.val+j.val)
def inputs : List ℕ := [0x800000000000c00000000000,0x10441051c50090cc30f3cf,0x101504cc45c030370ccccfc,0x400000000000c00000000000,0x46381050e0a0c63830f0f0f,0x103403b00ba0307c03f00ff0,0x3b8002eaa0003f8003fff000,0x2ecaa80000003ffffc000000]
def seeds : List Wire := [(false,0x800000000000c00000000000),(false,0x10441051c50090cc30f3cf),(false,0x101504cc45c030370ccccfc),(false,0x400000000000c00000000000),(false,0x46381050e0a0c63830f0f0f),(false,0x103403b00ba0307c03f00ff0),(false,0x3b8002eaa0003f8003fff000),(false,0x2ecaa80000003ffffc000000)]
set_option maxHeartbeats 10000000 in
theorem listed : ∀ i : Fin 48, seeds.map (read i.val)=List.ofFn (sample posBits i) ∧
    seeds.map (read (48+i.val))=List.ofFn (sample negBits i) := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem labels : ∀ i : Fin 48, target (sample posBits i)=true ∧ target (sample negBits i)=false := by decide +kernel
theorem essential : ∀ a∈inputs, ∃ i : Fin 48, ∀ b∈inputs, b.testBit i.val≠b.testBit (48+i.val) → b=a := by decide +kernel
theorem initial {k S} (live : Live 48 k S) (sub : ∀ a∈S,a∈inputs) : S=inputs.toFinset := by
  apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
  intro a ha
  obtain ⟨i,h⟩ := essential a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
  exact h b (sub b hb) sep ▸ hb
theorem trace (C : Circuit) (fan : FanInTwo C) (eq : circuitFun 8 C=target) :
    ∃ k≤C.gates.countP counted, Live 48 k inputs.toFinset := by
  let final := execute C.gates seeds
  let out := final.getD C.output zero
  have ev (i : ℕ) : read i out = C.eval (seeds.map (read i)) := by
    rw [show read i out = (final.map (read i)).getD C.output false from (read_get i final C.output).symm]
    rw [show final=execute C.gates seeds from rfl,execute_read i _ _ fan];rfl
  have result (x : Fin 8 → Bool) : C.eval (List.ofFn x)=target x := congrFun eq x
  have good : Good 48 out.2 := by
    intro i hi same
    let j : Fin 48 := ⟨i,hi⟩
    have diff : read i out=read (48+i) out := by
      change (out.1 != out.2.testBit i) = (out.1 != out.2.testBit (48+i))
      rw [same]
    have p := ev i;have n := ev (48+i)
    rw [(listed j).1,result,(labels j).1] at p
    rw [(listed j).2,result,(labels j).2] at n
    rw [p,n] at diff;contradiction
  have nz : out.2≠0 := by
    intro z;have bad := good 0 (by decide);simp [z] at bad
  have found : out.2∈ reps final := (get_simple final C.output).resolve_left nz
  obtain ⟨k,S,limit,live,sub⟩ := extract good nz C.gates seeds found
  have keep : ∀ a∈reps seeds, a≠0 → a∈inputs := by decide +kernel
  have stays : ∀ a∈S, a∈inputs := fun a ha => keep a (sub a ha) (liveNonzero live a ha)
  exact ⟨k,limit,initial live stays ▸ live⟩

def restricted : List ℕ := v0
def restrictRows : Projection 48 46 := pick (List.range 46) (by decide) (by decide) (by decide)
set_option maxHeartbeats 8000000 in
theorem core_floor : Wide 46 9 restricted := verifiedPin
theorem six_floor : Ban 48 11 inputs := viaCut restrictRows core_floor (by decide) (by decide +kernel) (by decide +kernel)
def witness : Circuit := ⟨[⟨.or,[0,7]⟩, ⟨.or,[5,7]⟩, ⟨.or,[0,1]⟩, ⟨.or,[1,6]⟩, ⟨.or,[6,7]⟩, ⟨.or,[3,5]⟩, ⟨.and,[10,12]⟩, ⟨.and,[2,9]⟩, ⟨.and,[4,11]⟩, ⟨.and,[13,8]⟩, ⟨.or,[14,15]⟩, ⟨.or,[18,16]⟩, ⟨.or,[19,17]⟩],20⟩
theorem wmono : Monotone2 witness := by simp [Monotone2,witness]
theorem wcomputes : ∀ x : Fin 8 → Bool, witness.eval (List.ofFn x) = target x := by decide +kernel
theorem binary_floor {C : Circuit} (fan : FanInTwo C) (d : ∀ x, C.eval (List.ofFn x) = target x) :
    12 ≤ C.gates.countP counted := by
  obtain ⟨k,le,live⟩ := trace C fan (funext d)
  by_contra! low
  exact six_floor k (by omega) live
theorem mono_enough : ∀ s, HasCircuitSize 8 target s →
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x, C.eval (List.ofFn x)=target x := by
  rintro s ⟨C,fan,sz,correct⟩
  by_cases hn : ∃ g ∈ C.gates, g.op = .not
  · obtain ⟨g,hg,hop⟩ := hn
    have low := binary_floor fan correct
    have lt : C.gates.countP counted < C.gates.length := by
      apply Nat.lt_of_le_of_ne List.countP_le_length
      intro equal
      have is := List.countP_eq_length.mp equal g hg
      simp [counted,hop] at is
    refine ⟨witness,wmono,?_,wcomputes⟩
    change C.gates.length ≤ s at sz
    change 13 ≤ s
    omega
  · refine ⟨C,?_,sz,correct⟩
    intro g hg
    obtain ⟨op,len⟩ := fan g hg
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.imp_right (fun h => h.resolve_right (fun e => hn ⟨g,hg,e⟩)),len⟩
end PEqualNP.Outside.L_meta_14776.Data

theorem PEqualNP.Outside.L_meta_14776 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fan _ computes
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gates, o⟩
  have size : PEqualNP.MetaComplexity.HasCircuitSize 8 PEqualNP.Outside.L_meta_14776.Data.target gates.length :=
    ⟨C,fan,le_rfl,computes⟩
  obtain ⟨D,mono,bound,correct⟩ := PEqualNP.Outside.L_meta_14776.Data.mono_enough gates.length size
  exact ⟨D.gates,D.output,mono,bound,correct⟩
