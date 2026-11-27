import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_11675

-- The free-negation trace checker and clique certificate are adapted from L_meta_10532.
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

def caseInputs : List ℕ := [16533043140244196525055,2147483648,9520900162536373279,8589934592,452242757947671739423,609337610714818314208,1218675221428629897216]
def projectRows : Projection 37 30 := pick [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29] rfl (by decide +kernel) (by decide)
theorem caseBound : Ban 37 8 caseInputs := viaCut projectRows petit0 (by decide) (by decide +kernel) (by decide +kernel)
def graph (x : Fin 7 → Bool) := decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
def posBits : ℕ := 0x4142464242447060c183054a952a5483060c182d1a3468d10a142850952a54a95
def negBits : ℕ := 0x10206020204004040500808080a0101010140202020280404040500808080a01
def sample (bank : ℕ) (i : Fin 37) (j : Fin 7) := bank.testBit (7*i.val+j.val)
def inputs : List ℕ := caseInputs
def seeds : List Wire := inputs.map (fun a => (false,a))
set_option maxHeartbeats 1000000 in
theorem listed : ∀ i : Fin 37, seeds.map (read i.val)=List.ofFn (sample posBits i) ∧
    seeds.map (read (37+i.val))=List.ofFn (sample negBits i) := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem labels : ∀ i : Fin 37, graph (sample posBits i)=true ∧ graph (sample negBits i)=false := by decide +kernel
theorem essential : ∀ a∈inputs, ∃ i : Fin 37, ∀ b∈inputs, b.testBit i.val≠b.testBit (37+i.val) → b=a := by decide +kernel
theorem initial {k S} (live : Live 37 k S) (sub : ∀ a∈S,a∈inputs) : S=inputs.toFinset := by
  apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
  intro a ha
  obtain ⟨i,h⟩ := essential a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
  exact h b (sub b hb) sep ▸ hb
theorem trace (C : Circuit) (fan : FanInTwo C) (eq : circuitFun 7 C=graph) :
    ∃ k≤C.gates.countP counted, Live 37 k inputs.toFinset := by
  let final := execute C.gates seeds
  let out := final.getD C.output zero
  have ev (i : ℕ) : read i out = C.eval (seeds.map (read i)) := by
    rw [show read i out = (final.map (read i)).getD C.output false from (read_get i final C.output).symm]
    rw [show final=execute C.gates seeds from rfl,execute_read i _ _ fan];rfl
  have result (x : Fin 7 → Bool) : C.eval (List.ofFn x)=graph x := congrFun eq x
  have good : Good 37 out.2 := by
    intro i hi same
    let j : Fin 37 := ⟨i,hi⟩
    have diff : read i out=read (37+i) out := by simp [read,same]
    have p := ev i;have n := ev (37+i)
    rw [(listed j).1,result,(labels j).1] at p
    rw [(listed j).2,result,(labels j).2] at n
    rw [p,n] at diff;contradiction
  have nz : out.2≠0 := by
    intro z;have bad := good 0 (by decide);simp [z] at bad
  have found : out.2∈ reps final := (get_simple final C.output).resolve_left nz
  obtain ⟨k,S,limit,live,sub⟩ := extract good nz C.gates seeds found
  have stays : ∀ a∈S, a∈inputs := by simpa [reps,seeds,List.map_map,Function.comp_def] using sub
  exact ⟨k,limit,initial live stays ▸ live⟩


def temoin : List Gate := [⟨.or, [0,2]⟩, ⟨.or, [0,1]⟩, ⟨.or, [4,5]⟩, ⟨.or, [3,5]⟩, ⟨.or, [5,6]⟩, ⟨.and, [9,8]⟩, ⟨.and, [11,7]⟩, ⟨.and, [6,10]⟩, ⟨.or, [12,13]⟩, ⟨.or, [15,14]⟩]
theorem temoin_ok : ∀ g ∈ temoin, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by simp [temoin]
set_option maxHeartbeats 2000000 in
theorem temoin_calc : ∀ x : Fin 7 → Bool, Circuit.eval ⟨temoin,16⟩ (List.ofFn x) = graph x := by decide +kernel
theorem lt_count {gs : List Gate} (h : ∃ g ∈ gs, g.op = .not) : gs.countP counted < gs.length := by
  apply Nat.lt_of_le_of_ne List.countP_le_length
  intro eq
  obtain ⟨g,hg,hop⟩ := h
  have bad := List.countP_eq_length.mp eq g hg
  simp [counted,hop] at bad

end PEqualNP.Outside.L_meta_11675

open PEqualNP.Outside.L_meta_11675 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in

theorem PEqualNP.Outside.L_meta_11675 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

