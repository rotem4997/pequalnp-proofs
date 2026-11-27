import PEqualNP.Defs

-- The signed live-wire calculus follows L-meta-10532. Pinning input 5 in either
-- direction leaves a five-input restriction that needs eight binary gates.
-- The two certificates below cover both restrictions.


namespace PEqualNP.Outside.L_meta_12325

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

end PEqualNP.Outside.L_meta_12325

namespace PEqualNP.Outside.L_meta_12325

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

end PEqualNP.Outside.L_meta_12325

namespace PEqualNP.Outside.L_meta_12325
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







end PEqualNP.Outside.L_meta_12325

namespace PEqualNP.Outside.L_meta_12325

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
end PEqualNP.Outside.L_meta_12325

namespace PEqualNP.Outside.L_meta_12325

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
end PEqualNP.Outside.L_meta_12325

namespace PEqualNP.Outside.L_meta_12325
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

end PEqualNP.Outside.L_meta_12325

namespace PEqualNP.Outside.L_meta_12325.B0
def f0 : ℕ := 0xe1b86e078fe3f
def f1 : ℕ := 0x62c5b1638f1fc7
def f2 : ℕ := 0x30368da1c0fe3f8
def f3 : ℕ := 0x5b4006dbff003ff
def f4 : ℕ := 0x6d9b6001ffffc00
def s0 : List ℕ := [f0,f1,f2,f3,f4]
def f5 : ℕ := 0x2018060081e07
def s1 : List ℕ := [f5,f0,f1,f2,f3,f4]
def rho0 : Weak 30 6 := signedPick 3 [3,4,13,14,20,21] (by decide) (by decide) (by decide)
def f6 : ℕ := 0xa3c
def f7 : ℕ := 0xb4c
def f8 : ℕ := 0xeb0
def s2 : List ℕ := [f6,f7,f8]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w0 : Wide 6 3 s2 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof1 : Ban 30 6 s1 := viaWeakCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f9 : ℕ := 0x6edfb7e3ffffff
def s3 : List ℕ := [f0,f1,f9,f2,f3,f4]
def rho1 : Weak 30 6 := signedPick 0 [0,1,10,11,20,21] (by decide) (by decide) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof2 : Ban 30 6 s3 := viaWeakCut rho1 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f10 : ℕ := 0x60c431038701c0
def s4 : List ℕ := [f0,f10,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof3 : Ban 30 6 s4 := viaWeakCut rho1 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f11 : ℕ := 0xc1a068070e038
def s5 : List ℕ := [f11,f0,f1,f2,f3,f4]
def rho2 : Weak 30 6 := signedPick 0 [0,2,10,12,23,24] (by decide) (by decide) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof4 : Ban 30 6 s5 := viaWeakCut rho2 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f12 : ℕ := 0x208820008e238
def s6 : List ℕ := [f12,f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof5 : Ban 30 6 s6 := viaWeakCut rho1 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f13 : ℕ := 0x30f7bdefc7fffff
def s7 : List ℕ := [f0,f1,f2,f13,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof6 : Ban 30 6 s7 := viaWeakCut rho1 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f14 : ℕ := 0x30160581c0701c0
def s8 : List ℕ := [f0,f1,f14,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof7 : Ban 30 6 s8 := viaWeakCut rho1 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f15 : ℕ := 0xc1304e0701c07
def s9 : List ℕ := [f15,f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof8 : Ban 30 6 s9 := viaWeakCut rho1 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f16 : ℕ := 0x24090000f03c0
def s10 : List ℕ := [f16,f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof9 : Ban 30 6 s10 := viaWeakCut rho1 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f17 : ℕ := 0x363edfb7f8fffff
def s11 : List ℕ := [f0,f1,f2,f17,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof10 : Ban 30 6 s11 := viaWeakCut rho2 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f18 : ℕ := 0x301284a1c00e038
def s12 : List ℕ := [f0,f1,f18,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof11 : Ban 30 6 s12 := viaWeakCut rho1 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f19 : ℕ := 0x60852163801c07
def s13 : List ℕ := [f0,f19,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof12 : Ban 30 6 s13 := viaWeakCut rho2 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f20 : ℕ := 0x40004a070023f
def s14 : List ℕ := [f20,f0,f1,f2,f3,f4]
def rho3 : Weak 30 6 := signedPick 6 [6,7,16,17,23,24] (by decide) (by decide) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof13 : Ban 30 6 s14 := viaWeakCut rho3 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f21 : ℕ := 0x5be1beffff8ffff
def s15 : List ℕ := [f0,f1,f2,f3,f21,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof14 : Ban 30 6 s15 := viaWeakCut rho1 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f22 : ℕ := 0x5b000691f8001c0
def s16 : List ℕ := [f0,f1,f2,f22,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof15 : Ban 30 6 s16 := viaWeakCut rho1 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f23 : ℕ := 0xa1b824008fc00
def s17 : List ℕ := [f23,f0,f1,f2,f3,f4]
def rho4 : Weak 30 6 := signedPick 1 [1,2,4,5,7,8] (by decide) (by decide) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof16 : Ban 30 6 s17 := viaWeakCut rho4 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f24 : ℕ := 0x200021238003c7
def s18 : List ℕ := [f0,f24,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof17 : Ban 30 6 s18 := viaWeakCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f25 : ℕ := 0x5f6c5fdffff1fff
def s19 : List ℕ := [f0,f1,f2,f3,f25,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof18 : Ban 30 6 s19 := viaWeakCut rho2 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f26 : ℕ := 0x594004c9c700038
def s20 : List ℕ := [f0,f1,f2,f26,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof19 : Ban 30 6 s20 := viaWeakCut rho2 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f27 : ℕ := 0x42c590400f1c00
def s21 : List ℕ := [f0,f27,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof20 : Ban 30 6 s21 := viaWeakCut rho4 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f28 : ℕ := 0x10000481c0003f8
def s22 : List ℕ := [f0,f1,f28,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof21 : Ban 30 6 s22 := viaWeakCut rho1 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f29 : ℕ := 0x7b768ffbfffe3ff
def s23 : List ℕ := [f0,f1,f2,f3,f4,f29]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof22 : Ban 30 6 s23 := viaWeakCut rho4 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f30 : ℕ := 0x4b40025a3f00007
def s24 : List ℕ := [f0,f1,f2,f30,f3,f4]
def rho5 : Weak 30 6 := signedPick 1 [1,2,20,22,23,25] (by decide) (by decide) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof23 : Ban 30 6 s24 := viaWeakCut rho5 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f31 : ℕ := 0x2036892000fe000
def s25 : List ℕ := [f0,f1,f31,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof24 : Ban 30 6 s25 := viaWeakCut rho1 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f32 : ℕ := 0x812000078fc00
def s26 : List ℕ := [f32,f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof25 : Ban 30 6 s26 := viaWeakCut rho4 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f33 : ℕ := 0x6dfbf86fffffe3f
def s27 : List ℕ := [f0,f1,f2,f3,f4,f33]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof26 : Ban 30 6 s27 := viaWeakCut rho1 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f34 : ℕ := 0x6d1a4001f870000
def s28 : List ℕ := [f0,f1,f2,f3,f34,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof27 : Ban 30 6 s28 := viaWeakCut rho1 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f35 : ℕ := 0x60986e000023f
def s29 : List ℕ := [f35,f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof28 : Ban 30 6 s29 := viaWeakCut rho3 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f36 : ℕ := 0x408400038f1c00
def s30 : List ℕ := [f0,f36,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof29 : Ban 30 6 s30 := viaWeakCut rho4 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f37 : ℕ := 0x6fbf7b17fffffc7
def s31 : List ℕ := [f0,f1,f2,f3,f4,f37]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof30 : Ban 30 6 s31 := viaWeakCut rho2 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f38 : ℕ := 0x69932001c70e000
def s32 : List ℕ := [f0,f1,f2,f3,f38,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof31 : Ban 30 6 s32 := viaWeakCut rho2 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f39 : ℕ := 0x2241b1600003c7
def s33 : List ℕ := [f0,f39,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof32 : Ban 30 6 s33 := viaWeakCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f40 : ℕ := 0x20120001c0fe000
def s34 : List ℕ := [f0,f1,f40,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof33 : Ban 30 6 s34 := viaWeakCut rho1 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f41 : ℕ := 0x7dbfeda1ffffff8
def s35 : List ℕ := [f0,f1,f2,f3,f4,f41]
def rho6 : Weak 30 6 := signedPick 3 [3,5,13,15,26,27] (by decide) (by decide) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof34 : Ban 30 6 s35 := viaWeakCut rho6 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f42 : ℕ := 0x4d8960003f01c00
def s36 : List ℕ := [f0,f1,f2,f42,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof35 : Ban 30 6 s36 := viaWeakCut rho4 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f43 : ℕ := 0x10248da000003f8
def s37 : List ℕ := [f0,f1,f43,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof36 : Ban 30 6 s37 := viaWeakCut rho1 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f44 : ℕ := 0x49000001ff00000
def s38 : List ℕ := [f0,f1,f2,f44,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof37 : Ban 30 6 s38 := viaWeakCut rho4 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f45 : ℕ := 0x7fdb66dbfffffff
def s39 : List ℕ := [f0,f1,f2,f3,f4,f45]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof38 : Ban 30 6 s39 := viaWeakCut rho4 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f46 : ℕ := 0x249b600000ffc00
def s40 : List ℕ := [f0,f1,f46,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof39 : Ban 30 6 s40 := viaWeakCut rho4 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f47 : ℕ := 0x124006da00003ff
def s41 : List ℕ := [f0,f1,f47,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof40 : Ban 30 6 s41 := viaWeakCut rho4 w0 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof0 : Ban 30 7 s0 := viaBranch (ws := [s1,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33,s34,s35,s36,s37,s38,s39,s40,s41])
  (consBan proof1 (consBan proof2 (consBan proof3 (consBan proof4 (consBan proof5 (consBan proof6 (consBan proof7 (consBan proof8 (consBan proof9 (consBan proof10 (consBan proof11 (consBan proof12 (consBan proof13 (consBan proof14 (consBan proof15 (consBan proof16 (consBan proof17 (consBan proof18 (consBan proof19 (consBan proof20 (consBan proof21 (consBan proof22 (consBan proof23 (consBan proof24 (consBan proof25 (consBan proof26 (consBan proof27 (consBan proof28 (consBan proof29 (consBan proof30 (consBan proof31 (consBan proof32 (consBan proof33 (consBan proof34 (consBan proof35 (consBan proof36 (consBan proof37 (consBan proof38 (consBan proof39 (consBan proof40 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
theorem cert6 : Ban 30 7 s0 := proof0
end PEqualNP.Outside.L_meta_12325.B0

namespace PEqualNP.Outside.L_meta_12325.B1
def f0 : ℕ := 0x61ba47c38fe93
def f1 : ℕ := 0x12c5c500cf1f1c
def f2 : ℕ := 0x4368e8030fe3e0
def f3 : ℕ := 0xa80012bff003ff
def f4 : ℕ := 0xfdb60003fffc00
def s0 : List ℕ := [f0,f1,f2,f3,f4]
def f5 : ℕ := 0x2018400081e10
def s1 : List ℕ := [f5,f0,f1,f2,f3,f4]
def rho0 : Weak 30 6 := signedPick 14 [14,15,20,21,24,25] (by decide) (by decide) (by decide)
def f6 : ℕ := 0xa3c
def f7 : ℕ := 0xb4c
def f8 : ℕ := 0xeb0
def s2 : List ℕ := [f6,f7,f8]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w0 : Wide 6 3 s2 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof1 : Ban 30 6 s1 := viaWeakCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f9 : ℕ := 0x16dfe57cffff9f
def s3 : List ℕ := [f0,f1,f9,f2,f3,f4]
def s4 : List ℕ := [f5,f9,f2,f3,f4]
def rho1 : Weak 30 10 := signedPick 14 [14,15,17,18,20,21,22,23,24,25] (by decide) (by decide) (by decide)
def f10 : ℕ := 0xa83f0
def f11 : ℕ := 0xbd4f0
def f12 : ℕ := 0xeab00
def s5 : List ℕ := [f10,f11,f12]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w1 : Wide 10 3 s5 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof3 : Ban 30 5 s4 := viaWeakCut rho1 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s6 : List ℕ := [f5,f1,f9,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof4 : Ban 30 5 s6 := viaSmall (by decide +kernel) (by decide)
def s7 : List ℕ := [f5,f0,f9,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof5 : Ban 30 5 s7 := viaSmall (by decide +kernel) (by decide)
def f13 : ℕ := 0x10c44100c7010c
def s8 : List ℕ := [f13,f1,f9,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof6 : Ban 30 5 s8 := viaSmall (by decide +kernel) (by decide)
def f14 : ℕ := 0x41a207c30e083
def s9 : List ℕ := [f14,f0,f9,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof7 : Ban 30 5 s9 := viaSmall (by decide +kernel) (by decide)
def s10 : List ℕ := [f0,f13,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof8 : Ban 30 5 s10 := viaSmall (by decide +kernel) (by decide)
def s11 : List ℕ := [f14,f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof9 : Ban 30 5 s11 := viaSmall (by decide +kernel) (by decide)
def f15 : ℕ := 0x477bec7f3ffff3
def s12 : List ℕ := [f1,f9,f2,f15,f3,f4]
def rho2 : Weak 30 12 := signedPick 11 [11,12,14,15,17,18,20,21,22,23,24,25] (by decide) (by decide) (by decide)
def f16 : ℕ := 0x428c3c
def f17 : ℕ := 0xa80fc0
def f18 : ℕ := 0xb92300
def f19 : ℕ := 0xea8c00
def f20 : ℕ := 0xeedccc
def s13 : List ℕ := [f16,f17,f18,f19,f20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w2 : Wide 12 4 s13 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof10 : Ban 30 5 s12 := viaWeakCut rho2 w2 (by decide) (by decide +kernel) (by decide +kernel)
def f21 : ℕ := 0x413047c301c13
def s14 : List ℕ := [f21,f1,f9,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof11 : Ban 30 5 s14 := viaSmall (by decide +kernel) (by decide)
def f22 : ℕ := 0x53eded03cffffc
def s15 : List ℕ := [f0,f9,f2,f22,f3,f4]
def f23 : ℕ := 0xac50c0
def f24 : ℕ := 0xfbaf30
def s16 : List ℕ := [f16,f17,f23,f19,f24]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w3 : Wide 12 4 s16 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof12 : Ban 30 5 s15 := viaWeakCut rho2 w3 (by decide) (by decide +kernel) (by decide +kernel)
def f25 : ℕ := 0x10850500c01c1c
def s17 : List ℕ := [f0,f25,f9,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof13 : Ban 30 5 s17 := viaSmall (by decide +kernel) (by decide)
def f26 : ℕ := 0x248e0000fe380
def s18 : List ℕ := [f26,f0,f1,f2,f3,f4]
def rho3 : Weak 30 6 := signedPick 11 [11,12,20,21,22,23] (by decide) (by decide) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w4 : Wide 6 2 s2 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof14 : Ban 30 5 s18 := viaWeakCut rho3 w4 (by decide) (by decide +kernel) (by decide +kernel)
def f27 : ℕ := 0x57ffed7fffffff
def s19 : List ℕ := [f0,f1,f2,f27,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof15 : Ban 30 5 s19 := viaSmall (by decide +kernel) (by decide)
def f28 : ℕ := 0x41200803000060
def s20 : List ℕ := [f0,f1,f28,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof16 : Ban 30 5 s20 := viaSmall (by decide +kernel) (by decide)
def f29 : ℕ := 0x1497057cf01c1f
def s21 : List ℕ := [f0,f1,f29,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof17 : Ban 30 5 s21 := viaSmall (by decide +kernel) (by decide)
def f30 : ℕ := 0xae1bb6fff8ffff
def s22 : List ℕ := [f1,f9,f2,f3,f30,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof18 : Ban 30 5 s22 := viaSmall (by decide +kernel) (by decide)
def f31 : ℕ := 0x61ba44008fc00
def s23 : List ℕ := [f31,f1,f9,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof19 : Ban 30 5 s23 := viaSmall (by decide +kernel) (by decide)
def f32 : ℕ := 0xbac5d7bfff1fff
def s24 : List ℕ := [f0,f9,f2,f3,f32,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof20 : Ban 30 5 s24 := viaSmall (by decide +kernel) (by decide)
def f33 : ℕ := 0x12c5c5000f1c00
def s25 : List ℕ := [f0,f33,f9,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof21 : Ban 30 5 s25 := viaSmall (by decide +kernel) (by decide)
def f34 : ℕ := 0x3cf0039f
def s26 : List ℕ := [f34,f0,f1,f2,f3,f4]
def rho4 : Weak 30 6 := signedPick 11 [11,12,14,15,17,18] (by decide) (by decide) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof22 : Ban 30 5 s26 := viaWeakCut rho4 w4 (by decide) (by decide +kernel) (by decide +kernel)
def f35 : ℕ := 0xbedff7ffffffff
def s27 : List ℕ := [f0,f1,f2,f3,f35,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof23 : Ban 30 5 s27 := viaSmall (by decide +kernel) (by decide)
def f36 : ℕ := 0xa8001283000060
def s28 : List ℕ := [f0,f1,f2,f36,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof24 : Ban 30 5 s28 := viaSmall (by decide +kernel) (by decide)
def f37 : ℕ := 0x16dfe5400ffc00
def s29 : List ℕ := [f0,f1,f37,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof25 : Ban 30 5 s29 := viaSmall (by decide +kernel) (by decide)
def f38 : ℕ := 0x412000038fc00
def s30 : List ℕ := [f38,f1,f9,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof26 : Ban 30 5 s30 := viaSmall (by decide +kernel) (by decide)
def f39 : ℕ := 0xf9a40003c70000
def s31 : List ℕ := [f1,f9,f2,f3,f39,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof27 : Ban 30 5 s31 := viaSmall (by decide +kernel) (by decide)
def f40 : ℕ := 0x10840000cf1c00
def s32 : List ℕ := [f0,f40,f9,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof28 : Ban 30 5 s32 := viaSmall (by decide +kernel) (by decide)
def f41 : ℕ := 0xed32000330e000
def s33 : List ℕ := [f0,f9,f2,f3,f41,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof29 : Ban 30 5 s33 := viaSmall (by decide +kernel) (by decide)
def f42 : ℕ := 0x14960000fffc00
def s34 : List ℕ := [f0,f1,f42,f2,f3]
def rho5 : Projection 30 16 := pick [0,1,2,3,4,10,11,12,20,21,22,23,26,27,28,29] (by decide) (by decide) (by decide)
def f43 : ℕ := 0x171f3f3
def f44 : ℕ := 0x4b40cfc
def f45 : ℕ := 0x5c00fe0
def f46 : ℕ := 0xa0aff1f
def s35 : List ℕ := [f43,f44,f45,f46]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w5 : Wide 16 4 s35 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof30 : Ban 30 5 s34 := viaCut rho5 w5 (by decide) (by decide +kernel) (by decide +kernel)
def s36 : List ℕ := [f0,f1,f42,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof31 : Ban 30 5 s36 := viaSmall (by decide +kernel) (by decide)
def s37 : List ℕ := [f0,f1,f42,f9,f2,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof32 : Ban 30 5 s37 := viaSmall (by decide +kernel) (by decide)
def f47 : ℕ := 0xffffe57fffff9f
def s38 : List ℕ := [f0,f1,f2,f3,f4,f47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof33 : Ban 30 5 s38 := viaSmall (by decide +kernel) (by decide)
def f48 : ℕ := 0xe9200003000000
def s39 : List ℕ := [f0,f1,f2,f3,f48,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof34 : Ban 30 5 s39 := viaSmall (by decide +kernel) (by decide)
def f49 : ℕ := 0x249e57c00039f
def s40 : List ℕ := [f49,f0,f1,f2,f3]
def rho6 : Projection 30 6 := pick [11,12,14,15,17,18] (by decide) (by decide) (by decide)
def f50 : ℕ := 0x14f
def f51 : ℕ := 0x4b3
def s41 : List ℕ := [f50,f51,f6]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w6 : Wide 6 3 s41 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof35 : Ban 30 5 s40 := viaCut rho6 w6 (by decide) (by decide +kernel) (by decide +kernel)
def s42 : List ℕ := [f49,f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof36 : Ban 30 5 s42 := viaWeakCut rho4 w4 (by decide) (by decide +kernel) (by decide +kernel)
def s43 : List ℕ := [f49,f0,f1,f9,f2,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof37 : Ban 30 5 s43 := viaSmall (by decide +kernel) (by decide)
def f52 : ℕ := 0xfdb612bfffffff
def s44 : List ℕ := [f0,f1,f9,f2,f3,f52]
def rho7 : Weak 30 8 := signedPick 1 [1,6,14,15,20,21,24,25] (by decide) (by decide) (by decide)
def f53 : ℕ := 0x48ce
def f54 : ℕ := 0x5c0c
def f55 : ℕ := 0xebc2
def s45 : List ℕ := [f53,f54,f55]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w7 : Wide 8 3 s45 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof38 : Ban 30 5 s44 := viaWeakCut rho7 w7 (by decide) (by decide +kernel) (by decide +kernel)
def f56 : ℕ := 0x55b600000ffc00
def s46 : List ℕ := [f0,f1,f9,f2,f56,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof39 : Ban 30 5 s46 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof2 : Ban 30 6 s3 := viaBranch (ws := [s4,s6,s7,s8,s9,s10,s11,s12,s14,s15,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33,s34,s36,s37,s38,s39,s40,s42,s43,s44,s46])
  (consBan proof3 (consBan proof4 (consBan proof5 (consBan proof6 (consBan proof7 (consBan proof8 (consBan proof9 (consBan proof10 (consBan proof11 (consBan proof12 (consBan proof13 (consBan proof14 (consBan proof15 (consBan proof16 (consBan proof17 (consBan proof18 (consBan proof19 (consBan proof20 (consBan proof21 (consBan proof22 (consBan proof23 (consBan proof24 (consBan proof25 (consBan proof26 (consBan proof27 (consBan proof28 (consBan proof29 (consBan proof30 (consBan proof31 (consBan proof32 (consBan proof33 (consBan proof34 (consBan proof35 (consBan proof36 (consBan proof37 (consBan proof38 (consBan proof39 (nilBan _ _))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof40 : Ban 30 6 s10 := viaWeakCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def rho8 : Weak 30 6 := signedPick 17 [17,18,22,23,24,25] (by decide) (by decide) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof41 : Ban 30 6 s11 := viaWeakCut rho8 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f57 : ℕ := 0x208a00008e280
def s47 : List ℕ := [f57,f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof42 : Ban 30 6 s47 := viaWeakCut rho3 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s48 : List ℕ := [f0,f1,f2,f15,f3,f4]
def s49 : List ℕ := [f14,f1,f2,f15,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof44 : Ban 30 5 s49 := viaSmall (by decide +kernel) (by decide)
def s50 : List ℕ := [f57,f1,f15,f3,f4]
def rho9 : Weak 30 10 := signedPick 11 [11,12,17,18,20,21,22,23,24,25] (by decide) (by decide) (by decide)
def f58 : ℕ := 0xb98c0
def f59 : ℕ := 0xee730
def s51 : List ℕ := [f10,f58,f59]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w8 : Wide 10 3 s51 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof45 : Ban 30 5 s50 := viaWeakCut rho9 w8 (by decide) (by decide +kernel) (by decide +kernel)
def s52 : List ℕ := [f57,f1,f2,f15,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof46 : Ban 30 5 s52 := viaSmall (by decide +kernel) (by decide)
def s53 : List ℕ := [f57,f0,f1,f15,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof47 : Ban 30 5 s53 := viaSmall (by decide +kernel) (by decide)
def f60 : ℕ := 0x41604803070160
def s54 : List ℕ := [f1,f60,f2,f15,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof48 : Ban 30 5 s54 := viaSmall (by decide +kernel) (by decide)
def s55 : List ℕ := [f21,f0,f1,f15,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof49 : Ban 30 5 s55 := viaSmall (by decide +kernel) (by decide)
def s56 : List ℕ := [f0,f1,f15,f22,f3,f4]
def s57 : List ℕ := [f17,f23,f18,f20,f24]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w9 : Wide 12 4 s57 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof50 : Ban 30 5 s56 := viaWeakCut rho2 w9 (by decide) (by decide +kernel) (by decide +kernel)
def f61 : ℕ := 0x4128280300e0e0
def s58 : List ℕ := [f0,f1,f61,f15,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof51 : Ban 30 5 s58 := viaSmall (by decide +kernel) (by decide)
def s59 : List ℕ := [f0,f1,f60,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof52 : Ban 30 5 s59 := viaSmall (by decide +kernel) (by decide)
def f62 : ℕ := 0x241c4000f1f10
def s60 : List ℕ := [f62,f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof53 : Ban 30 5 s60 := viaWeakCut rho0 w4 (by decide) (by decide +kernel) (by decide +kernel)
def f63 : ℕ := 0x453a287f30e0e3
def s61 : List ℕ := [f0,f1,f2,f63,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof54 : Ban 30 5 s61 := viaSmall (by decide +kernel) (by decide)
def f64 : ℕ := 0x10840100c0000c
def s62 : List ℕ := [f0,f64,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof55 : Ban 30 5 s62 := viaSmall (by decide +kernel) (by decide)
def s63 : List ℕ := [f21,f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof56 : Ban 30 5 s63 := viaSmall (by decide +kernel) (by decide)
def s64 : List ℕ := [f1,f2,f15,f3,f30,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof57 : Ban 30 5 s64 := viaSmall (by decide +kernel) (by decide)
def s65 : List ℕ := [f31,f1,f2,f15,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof58 : Ban 30 5 s65 := viaSmall (by decide +kernel) (by decide)
def f65 : ℕ := 0xeb68fabfffe3ff
def s66 : List ℕ := [f0,f1,f15,f3,f65,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof59 : Ban 30 5 s66 := viaSmall (by decide +kernel) (by decide)
def f66 : ℕ := 0x4368e8000fe000
def s67 : List ℕ := [f0,f1,f66,f15,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof60 : Ban 30 5 s67 := viaSmall (by decide +kernel) (by decide)
def f67 : ℕ := 0x3f3003f3
def s68 : List ℕ := [f67,f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof61 : Ban 30 5 s68 := viaWeakCut rho4 w4 (by decide) (by decide +kernel) (by decide +kernel)
def f68 : ℕ := 0xef7bfeffffffff
def s69 : List ℕ := [f0,f1,f2,f3,f68,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof62 : Ban 30 5 s69 := viaSmall (by decide +kernel) (by decide)
def f69 : ℕ := 0xa8001280c0000c
def s70 : List ℕ := [f0,f1,f2,f69,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof63 : Ban 30 5 s70 := viaSmall (by decide +kernel) (by decide)
def f70 : ℕ := 0x477bec400ffc00
def s71 : List ℕ := [f0,f1,f2,f70,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof64 : Ban 30 5 s71 := viaSmall (by decide +kernel) (by decide)
def s72 : List ℕ := [f38,f1,f2,f15,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof65 : Ban 30 5 s72 := viaSmall (by decide +kernel) (by decide)
def s73 : List ℕ := [f1,f2,f15,f3,f39,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof66 : Ban 30 5 s73 := viaSmall (by decide +kernel) (by decide)
def f71 : ℕ := 0x412000030fe000
def s74 : List ℕ := [f0,f1,f71,f15,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof67 : Ban 30 5 s74 := viaSmall (by decide +kernel) (by decide)
def f72 : ℕ := 0xbc960000f01c00
def s75 : List ℕ := [f0,f1,f15,f3,f72,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof68 : Ban 30 5 s75 := viaSmall (by decide +kernel) (by decide)
def f73 : ℕ := 0x453200033ffc00
def s76 : List ℕ := [f0,f1,f2,f73,f3]
def rho10 : Projection 30 16 := pick [0,1,5,6,7,13,14,15,20,21,24,25,26,27,28,29] (by decide) (by decide) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof69 : Ban 30 5 s76 := viaCut rho10 w5 (by decide) (by decide +kernel) (by decide +kernel)
def s77 : List ℕ := [f0,f1,f2,f73,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof70 : Ban 30 5 s77 := viaSmall (by decide +kernel) (by decide)
def s78 : List ℕ := [f0,f1,f2,f73,f15,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof71 : Ban 30 5 s78 := viaSmall (by decide +kernel) (by decide)
def f74 : ℕ := 0xffffec7ffffff3
def s79 : List ℕ := [f0,f1,f2,f3,f4,f74]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof72 : Ban 30 5 s79 := viaSmall (by decide +kernel) (by decide)
def f75 : ℕ := 0xb8840000c00000
def s80 : List ℕ := [f0,f1,f2,f3,f75,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof73 : Ban 30 5 s80 := viaSmall (by decide +kernel) (by decide)
def f76 : ℕ := 0x249ec7c0003f3
def s81 : List ℕ := [f76,f0,f1,f2,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof74 : Ban 30 5 s81 := viaCut rho6 w6 (by decide) (by decide +kernel) (by decide +kernel)
def s82 : List ℕ := [f76,f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof75 : Ban 30 5 s82 := viaWeakCut rho4 w4 (by decide) (by decide +kernel) (by decide +kernel)
def s83 : List ℕ := [f76,f0,f1,f2,f15,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof76 : Ban 30 5 s83 := viaSmall (by decide +kernel) (by decide)
def s84 : List ℕ := [f0,f1,f2,f15,f3,f52]
def rho11 : Weak 30 8 := signedPick 1 [1,3,11,12,20,21,22,23] (by decide) (by decide) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof77 : Ban 30 5 s84 := viaWeakCut rho11 w7 (by decide) (by decide +kernel) (by decide +kernel)
def s85 : List ℕ := [f0,f1,f2,f15,f56,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof78 : Ban 30 5 s85 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof43 : Ban 30 6 s48 := viaBranch (ws := [s12,s49,s50,s52,s53,s54,s55,s56,s58,s59,s60,s19,s61,s62,s63,s64,s65,s66,s67,s68,s69,s70,s71,s72,s73,s74,s75,s76,s77,s78,s79,s80,s81,s82,s83,s84,s85])
  (consBan proof10 (consBan proof44 (consBan proof45 (consBan proof46 (consBan proof47 (consBan proof48 (consBan proof49 (consBan proof50 (consBan proof51 (consBan proof52 (consBan proof53 (consBan proof15 (consBan proof54 (consBan proof55 (consBan proof56 (consBan proof57 (consBan proof58 (consBan proof59 (consBan proof60 (consBan proof61 (consBan proof62 (consBan proof63 (consBan proof64 (consBan proof65 (consBan proof66 (consBan proof67 (consBan proof68 (consBan proof69 (consBan proof70 (consBan proof71 (consBan proof72 (consBan proof73 (consBan proof74 (consBan proof75 (consBan proof76 (consBan proof77 (consBan proof78 (nilBan _ _))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof79 : Ban 30 6 s59 := viaWeakCut rho3 w0 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof80 : Ban 30 6 s63 := viaWeakCut rho8 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f77 : ℕ := 0x240c0000f0300
def s86 : List ℕ := [f77,f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof81 : Ban 30 6 s86 := viaWeakCut rho3 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s87 : List ℕ := [f0,f1,f2,f22,f3,f4]
def s88 : List ℕ := [f0,f13,f2,f22,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof83 : Ban 30 5 s88 := viaSmall (by decide +kernel) (by decide)
def s89 : List ℕ := [f0,f1,f60,f22,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof84 : Ban 30 5 s89 := viaSmall (by decide +kernel) (by decide)
def s90 : List ℕ := [f77,f0,f22,f3,f4]
def rho12 : Weak 30 10 := signedPick 11 [11,12,14,15,20,21,22,23,24,25] (by decide) (by decide) (by decide)
def f78 : ℕ := 0xad430
def f79 : ℕ := 0xfabc0
def s91 : List ℕ := [f10,f78,f79]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w10 : Wide 10 3 s91 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof85 : Ban 30 5 s90 := viaWeakCut rho12 w10 (by decide) (by decide +kernel) (by decide +kernel)
def s92 : List ℕ := [f77,f0,f2,f22,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof86 : Ban 30 5 s92 := viaSmall (by decide +kernel) (by decide)
def s93 : List ℕ := [f77,f0,f1,f22,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof87 : Ban 30 5 s93 := viaSmall (by decide +kernel) (by decide)
def s94 : List ℕ := [f0,f61,f2,f22,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof88 : Ban 30 5 s94 := viaSmall (by decide +kernel) (by decide)
def s95 : List ℕ := [f0,f25,f1,f22,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof89 : Ban 30 5 s95 := viaSmall (by decide +kernel) (by decide)
def f80 : ℕ := 0x209a40008fe90
def s96 : List ℕ := [f80,f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof90 : Ban 30 5 s96 := viaWeakCut rho8 w4 (by decide) (by decide +kernel) (by decide +kernel)
def f81 : ℕ := 0x51e44903c7016c
def s97 : List ℕ := [f0,f1,f2,f81,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof91 : Ban 30 5 s97 := viaSmall (by decide +kernel) (by decide)
def f82 : ℕ := 0x412007c300003
def s98 : List ℕ := [f82,f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof92 : Ban 30 5 s98 := viaSmall (by decide +kernel) (by decide)
def s99 : List ℕ := [f0,f1,f61,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof93 : Ban 30 5 s99 := viaSmall (by decide +kernel) (by decide)
def s100 : List ℕ := [f0,f25,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof94 : Ban 30 5 s100 := viaSmall (by decide +kernel) (by decide)
def s101 : List ℕ := [f0,f2,f22,f3,f32,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof95 : Ban 30 5 s101 := viaSmall (by decide +kernel) (by decide)
def s102 : List ℕ := [f0,f33,f2,f22,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof96 : Ban 30 5 s102 := viaSmall (by decide +kernel) (by decide)
def s103 : List ℕ := [f0,f1,f22,f3,f65,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof97 : Ban 30 5 s103 := viaSmall (by decide +kernel) (by decide)
def s104 : List ℕ := [f0,f1,f66,f22,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof98 : Ban 30 5 s104 := viaSmall (by decide +kernel) (by decide)
def f83 : ℕ := 0x3c003fc
def s105 : List ℕ := [f83,f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof99 : Ban 30 5 s105 := viaWeakCut rho4 w4 (by decide) (by decide +kernel) (by decide +kernel)
def f84 : ℕ := 0xfbedffbfffffff
def s106 : List ℕ := [f0,f1,f2,f3,f84,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof100 : Ban 30 5 s106 := viaSmall (by decide +kernel) (by decide)
def f85 : ℕ := 0xa80012bc300003
def s107 : List ℕ := [f0,f1,f2,f85,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof101 : Ban 30 5 s107 := viaSmall (by decide +kernel) (by decide)
def f86 : ℕ := 0x53eded000ffc00
def s108 : List ℕ := [f0,f1,f2,f86,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof102 : Ban 30 5 s108 := viaSmall (by decide +kernel) (by decide)
def s109 : List ℕ := [f0,f40,f2,f22,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof103 : Ban 30 5 s109 := viaSmall (by decide +kernel) (by decide)
def s110 : List ℕ := [f0,f2,f22,f3,f41,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof104 : Ban 30 5 s110 := viaSmall (by decide +kernel) (by decide)
def s111 : List ℕ := [f0,f1,f71,f22,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof105 : Ban 30 5 s111 := viaSmall (by decide +kernel) (by decide)
def s112 : List ℕ := [f0,f1,f22,f3,f72,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof106 : Ban 30 5 s112 := viaSmall (by decide +kernel) (by decide)
def f87 : ℕ := 0x51a40003cffc00
def s113 : List ℕ := [f0,f1,f2,f87,f3]
def rho13 : Projection 30 12 := pick [2,3,5,6,8,16,17,18,22,23,24,25] (by decide) (by decide) (by decide)
def f88 : ℕ := 0x1713f3
def f89 : ℕ := 0x4b4cfc
def f90 : ℕ := 0x5c0fe0
def f91 : ℕ := 0xa0af1f
def s114 : List ℕ := [f88,f89,f90,f91]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w11 : Wide 12 4 s114 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof107 : Ban 30 5 s113 := viaCut rho13 w11 (by decide) (by decide +kernel) (by decide +kernel)
def s115 : List ℕ := [f0,f1,f2,f87,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof108 : Ban 30 5 s115 := viaSmall (by decide +kernel) (by decide)
def s116 : List ℕ := [f0,f1,f2,f87,f22,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof109 : Ban 30 5 s116 := viaSmall (by decide +kernel) (by decide)
def f92 : ℕ := 0xffffed03fffffc
def s117 : List ℕ := [f0,f1,f2,f3,f4,f92]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof110 : Ban 30 5 s117 := viaSmall (by decide +kernel) (by decide)
def f93 : ℕ := 0xac120000300000
def s118 : List ℕ := [f0,f1,f2,f3,f93,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof111 : Ban 30 5 s118 := viaSmall (by decide +kernel) (by decide)
def f94 : ℕ := 0x249ed000003fc
def s119 : List ℕ := [f94,f0,f1,f2,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof112 : Ban 30 5 s119 := viaCut rho6 w6 (by decide) (by decide +kernel) (by decide +kernel)
def s120 : List ℕ := [f94,f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof113 : Ban 30 5 s120 := viaWeakCut rho4 w4 (by decide) (by decide +kernel) (by decide +kernel)
def s121 : List ℕ := [f94,f0,f1,f2,f22,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof114 : Ban 30 5 s121 := viaSmall (by decide +kernel) (by decide)
def s122 : List ℕ := [f0,f1,f2,f22,f3,f52]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof115 : Ban 30 5 s122 := viaWeakCut rho11 w7 (by decide) (by decide +kernel) (by decide +kernel)
def s123 : List ℕ := [f0,f1,f2,f22,f56,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof116 : Ban 30 5 s123 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof82 : Ban 30 6 s87 := viaBranch (ws := [s15,s88,s56,s89,s90,s92,s93,s94,s95,s96,s19,s97,s98,s99,s100,s101,s102,s103,s104,s105,s106,s107,s108,s109,s110,s111,s112,s113,s115,s116,s117,s118,s119,s120,s121,s122,s123])
  (consBan proof12 (consBan proof83 (consBan proof50 (consBan proof84 (consBan proof85 (consBan proof86 (consBan proof87 (consBan proof88 (consBan proof89 (consBan proof90 (consBan proof15 (consBan proof91 (consBan proof92 (consBan proof93 (consBan proof94 (consBan proof95 (consBan proof96 (consBan proof97 (consBan proof98 (consBan proof99 (consBan proof100 (consBan proof101 (consBan proof102 (consBan proof103 (consBan proof104 (consBan proof105 (consBan proof106 (consBan proof107 (consBan proof108 (consBan proof109 (consBan proof110 (consBan proof111 (consBan proof112 (consBan proof113 (consBan proof114 (consBan proof115 (consBan proof116 (nilBan _ _))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof117 : Ban 30 6 s99 := viaWeakCut rho3 w0 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof118 : Ban 30 6 s100 := viaWeakCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f95 : ℕ := 0x3c300293
def s124 : List ℕ := [f95,f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof119 : Ban 30 6 s124 := viaWeakCut rho4 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s125 : List ℕ := [f0,f1,f2,f3,f30,f4]
def s126 : List ℕ := [f14,f1,f2,f3,f30,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof121 : Ban 30 5 s126 := viaSmall (by decide +kernel) (by decide)
def s127 : List ℕ := [f21,f1,f2,f3,f30,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof122 : Ban 30 5 s127 := viaSmall (by decide +kernel) (by decide)
def s128 : List ℕ := [f95,f1,f2,f30,f4]
def rho14 : Weak 30 10 := signedPick 11 [11,12,14,15,17,18,22,23,24,25] (by decide) (by decide) (by decide)
def f96 : ℕ := 0x4a33c
def f97 : ℕ := 0x5e830
def f98 : ℕ := 0xeb70c
def s129 : List ℕ := [f96,f97,f98]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w12 : Wide 10 3 s129 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof123 : Ban 30 5 s128 := viaWeakCut rho14 w12 (by decide) (by decide +kernel) (by decide +kernel)
def s130 : List ℕ := [f95,f1,f2,f3,f30,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof124 : Ban 30 5 s130 := viaWeakCut rho4 w4 (by decide) (by decide +kernel) (by decide +kernel)
def s131 : List ℕ := [f95,f0,f1,f2,f30,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof125 : Ban 30 5 s131 := viaSmall (by decide +kernel) (by decide)
def f99 : ℕ := 0xa8001283c0016c
def s132 : List ℕ := [f1,f2,f99,f3,f30,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof126 : Ban 30 5 s132 := viaSmall (by decide +kernel) (by decide)
def s133 : List ℕ := [f31,f0,f1,f2,f30,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof127 : Ban 30 5 s133 := viaSmall (by decide +kernel) (by decide)
def s134 : List ℕ := [f0,f1,f2,f99,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof128 : Ban 30 5 s134 := viaSmall (by decide +kernel) (by decide)
def f100 : ℕ := 0x2018400c81f1c
def s135 : List ℕ := [f100,f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof129 : Ban 30 5 s135 := viaSmall (by decide +kernel) (by decide)
def f101 : ℕ := 0xac1a32ff30e0e3
def s136 : List ℕ := [f0,f1,f2,f3,f101,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof130 : Ban 30 5 s136 := viaSmall (by decide +kernel) (by decide)
def f102 : ℕ := 0x10c44100070000
def s137 : List ℕ := [f0,f102,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof131 : Ban 30 5 s137 := viaSmall (by decide +kernel) (by decide)
def f103 : ℕ := 0x208a00308e3e0
def s138 : List ℕ := [f103,f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof132 : Ban 30 5 s138 := viaSmall (by decide +kernel) (by decide)
def f104 : ℕ := 0xac1316fcf01c1f
def s139 : List ℕ := [f0,f1,f2,f3,f104,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof133 : Ban 30 5 s139 := viaSmall (by decide +kernel) (by decide)
def f105 : ℕ := 0x41604800070000
def s140 : List ℕ := [f0,f1,f105,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof134 : Ban 30 5 s140 := viaSmall (by decide +kernel) (by decide)
def s141 : List ℕ := [f31,f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof135 : Ban 30 5 s141 := viaSmall (by decide +kernel) (by decide)
def s142 : List ℕ := [f0,f1,f2,f3,f30,f52]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof136 : Ban 30 5 s142 := viaSmall (by decide +kernel) (by decide)
def s143 : List ℕ := [f0,f1,f2,f56,f3,f30]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof137 : Ban 30 5 s143 := viaSmall (by decide +kernel) (by decide)
def f106 : ℕ := 0xac120003f8fc00
def s144 : List ℕ := [f0,f1,f2,f3,f106,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof138 : Ban 30 5 s144 := viaSmall (by decide +kernel) (by decide)
def f107 : ℕ := 0xffbfb6ffffffff
def s145 : List ℕ := [f0,f1,f2,f3,f4,f107]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof139 : Ban 30 5 s145 := viaSmall (by decide +kernel) (by decide)
def f108 : ℕ := 0x51a40000070000
def s146 : List ℕ := [f0,f1,f2,f108,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof140 : Ban 30 5 s146 := viaSmall (by decide +kernel) (by decide)
def f109 : ℕ := 0x209b6fc0003ff
def s147 : List ℕ := [f109,f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof141 : Ban 30 5 s147 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof120 : Ban 30 6 s125 := viaBranch (ws := [s22,s126,s64,s127,s128,s130,s131,s132,s133,s134,s135,s27,s136,s137,s138,s69,s139,s140,s141,s142,s143,s144,s145,s146,s147])
  (consBan proof18 (consBan proof121 (consBan proof57 (consBan proof122 (consBan proof123 (consBan proof124 (consBan proof125 (consBan proof126 (consBan proof127 (consBan proof128 (consBan proof129 (consBan proof23 (consBan proof130 (consBan proof131 (consBan proof132 (consBan proof62 (consBan proof133 (consBan proof134 (consBan proof135 (consBan proof136 (consBan proof137 (consBan proof138 (consBan proof139 (consBan proof140 (consBan proof141 (nilBan _ _))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof142 : Ban 30 6 s134 := viaWeakCut rho4 w0 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof143 : Ban 30 6 s141 := viaWeakCut rho8 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f110 : ℕ := 0xc0031c
def s148 : List ℕ := [f110,f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof144 : Ban 30 6 s148 := viaWeakCut rho4 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s149 : List ℕ := [f0,f1,f2,f3,f32,f4]
def s150 : List ℕ := [f0,f13,f2,f3,f32,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof146 : Ban 30 5 s150 := viaSmall (by decide +kernel) (by decide)
def s151 : List ℕ := [f0,f25,f2,f3,f32,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof147 : Ban 30 5 s151 := viaSmall (by decide +kernel) (by decide)
def s152 : List ℕ := [f110,f0,f2,f32,f4]
def rho15 : Weak 30 10 := signedPick 11 [11,12,14,15,17,18,20,21,24,25] (by decide) (by decide) (by decide)
def f111 : ℕ := 0x5b40c
def f112 : ℕ := 0xeeb30
def s153 : List ℕ := [f96,f111,f112]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w13 : Wide 10 3 s153 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof148 : Ban 30 5 s152 := viaWeakCut rho15 w13 (by decide) (by decide +kernel) (by decide +kernel)
def s154 : List ℕ := [f110,f0,f2,f3,f32,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof149 : Ban 30 5 s154 := viaWeakCut rho4 w4 (by decide) (by decide +kernel) (by decide +kernel)
def s155 : List ℕ := [f110,f0,f1,f2,f32,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof150 : Ban 30 5 s155 := viaSmall (by decide +kernel) (by decide)
def f113 : ℕ := 0xa80012bf3000e3
def s156 : List ℕ := [f0,f2,f113,f3,f32,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof151 : Ban 30 5 s156 := viaSmall (by decide +kernel) (by decide)
def s157 : List ℕ := [f0,f33,f1,f2,f32,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof152 : Ban 30 5 s157 := viaSmall (by decide +kernel) (by decide)
def f114 : ℕ := 0x201843c381e93
def s158 : List ℕ := [f114,f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof153 : Ban 30 5 s158 := viaSmall (by decide +kernel) (by decide)
def f115 : ℕ := 0xb8c45383c7016c
def s159 : List ℕ := [f0,f1,f2,f3,f115,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof154 : Ban 30 5 s159 := viaSmall (by decide +kernel) (by decide)
def f116 : ℕ := 0x41a204000e000
def s160 : List ℕ := [f116,f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof155 : Ban 30 5 s160 := viaSmall (by decide +kernel) (by decide)
def s161 : List ℕ := [f0,f1,f2,f113,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof156 : Ban 30 5 s161 := viaSmall (by decide +kernel) (by decide)
def f117 : ℕ := 0x240c0030f03e0
def s162 : List ℕ := [f117,f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof157 : Ban 30 5 s162 := viaSmall (by decide +kernel) (by decide)
def f118 : ℕ := 0xb88517bcf01c1f
def s163 : List ℕ := [f0,f1,f2,f3,f118,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof158 : Ban 30 5 s163 := viaSmall (by decide +kernel) (by decide)
def f119 : ℕ := 0x4128280000e000
def s164 : List ℕ := [f0,f1,f119,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof159 : Ban 30 5 s164 := viaSmall (by decide +kernel) (by decide)
def s165 : List ℕ := [f0,f33,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof160 : Ban 30 5 s165 := viaSmall (by decide +kernel) (by decide)
def s166 : List ℕ := [f0,f1,f2,f3,f32,f52]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof161 : Ban 30 5 s166 := viaSmall (by decide +kernel) (by decide)
def s167 : List ℕ := [f0,f1,f2,f56,f3,f32]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof162 : Ban 30 5 s167 := viaSmall (by decide +kernel) (by decide)
def f120 : ℕ := 0xb8840003ff1c00
def s168 : List ℕ := [f0,f1,f2,f3,f120,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof163 : Ban 30 5 s168 := viaSmall (by decide +kernel) (by decide)
def f121 : ℕ := 0xfff7d7bfffffff
def s169 : List ℕ := [f0,f1,f2,f3,f4,f121]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof164 : Ban 30 5 s169 := viaSmall (by decide +kernel) (by decide)
def f122 : ℕ := 0x4532000000e000
def s170 : List ℕ := [f0,f1,f2,f122,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof165 : Ban 30 5 s170 := viaSmall (by decide +kernel) (by decide)
def f123 : ℕ := 0x241d7bc0003ff
def s171 : List ℕ := [f123,f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof166 : Ban 30 5 s171 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof145 : Ban 30 6 s149 := viaBranch (ws := [s24,s150,s101,s151,s152,s154,s155,s156,s157,s158,s27,s159,s160,s161,s162,s106,s163,s164,s165,s166,s167,s168,s169,s170,s171])
  (consBan proof20 (consBan proof146 (consBan proof95 (consBan proof147 (consBan proof148 (consBan proof149 (consBan proof150 (consBan proof151 (consBan proof152 (consBan proof153 (consBan proof23 (consBan proof154 (consBan proof155 (consBan proof156 (consBan proof157 (consBan proof100 (consBan proof158 (consBan proof159 (consBan proof160 (consBan proof161 (consBan proof162 (consBan proof163 (consBan proof164 (consBan proof165 (consBan proof166 (nilBan _ _))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof167 : Ban 30 6 s161 := viaWeakCut rho4 w0 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof168 : Ban 30 6 s165 := viaWeakCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f124 : ℕ := 0x30003e0
def s172 : List ℕ := [f124,f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof169 : Ban 30 6 s172 := viaWeakCut rho4 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s173 : List ℕ := [f0,f1,f2,f3,f65,f4]
def s174 : List ℕ := [f0,f1,f60,f3,f65,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof171 : Ban 30 5 s174 := viaSmall (by decide +kernel) (by decide)
def s175 : List ℕ := [f0,f1,f61,f3,f65,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof172 : Ban 30 5 s175 := viaSmall (by decide +kernel) (by decide)
def s176 : List ℕ := [f124,f0,f1,f65,f4]
def rho16 : Weak 30 10 := signedPick 11 [11,12,14,15,17,18,20,21,22,23] (by decide) (by decide) (by decide)
def f125 : ℕ := 0xaa3fc
def f126 : ℕ := 0xbb4cc
def s177 : List ℕ := [f125,f126,f112]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w14 : Wide 10 3 s177 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof173 : Ban 30 5 s176 := viaWeakCut rho16 w14 (by decide) (by decide +kernel) (by decide +kernel)
def s178 : List ℕ := [f124,f0,f1,f3,f65,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof174 : Ban 30 5 s178 := viaWeakCut rho4 w4 (by decide) (by decide +kernel) (by decide +kernel)
def s179 : List ℕ := [f124,f0,f1,f2,f65,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof175 : Ban 30 5 s179 := viaSmall (by decide +kernel) (by decide)
def f127 : ℕ := 0xa80012bcf0001f
def s180 : List ℕ := [f0,f1,f127,f3,f65,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof176 : Ban 30 5 s180 := viaSmall (by decide +kernel) (by decide)
def s181 : List ℕ := [f0,f1,f66,f2,f65,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof177 : Ban 30 5 s181 := viaSmall (by decide +kernel) (by decide)
def f128 : ℕ := 0x208a03c38e293
def s182 : List ℕ := [f128,f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof178 : Ban 30 5 s182 := viaSmall (by decide +kernel) (by decide)
def f129 : ℕ := 0xe9605a83c7016c
def s183 : List ℕ := [f0,f1,f2,f3,f129,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof179 : Ban 30 5 s183 := viaSmall (by decide +kernel) (by decide)
def f130 : ℕ := 0x4130440001c00
def s184 : List ℕ := [f130,f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof180 : Ban 30 5 s184 := viaSmall (by decide +kernel) (by decide)
def f131 : ℕ := 0x240c000cf031c
def s185 : List ℕ := [f131,f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof181 : Ban 30 5 s185 := viaSmall (by decide +kernel) (by decide)
def f132 : ℕ := 0xe9283abf30e0e3
def s186 : List ℕ := [f0,f1,f2,f3,f132,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof182 : Ban 30 5 s186 := viaSmall (by decide +kernel) (by decide)
def f133 : ℕ := 0x10850500001c00
def s187 : List ℕ := [f0,f133,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof183 : Ban 30 5 s187 := viaSmall (by decide +kernel) (by decide)
def s188 : List ℕ := [f0,f1,f2,f127,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof184 : Ban 30 5 s188 := viaSmall (by decide +kernel) (by decide)
def s189 : List ℕ := [f0,f1,f66,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof185 : Ban 30 5 s189 := viaSmall (by decide +kernel) (by decide)
def s190 : List ℕ := [f0,f1,f2,f3,f65,f52]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof186 : Ban 30 5 s190 := viaSmall (by decide +kernel) (by decide)
def s191 : List ℕ := [f0,f1,f2,f56,f3,f65]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof187 : Ban 30 5 s191 := viaSmall (by decide +kernel) (by decide)
def f134 : ℕ := 0xe9200003ffe000
def s192 : List ℕ := [f0,f1,f2,f3,f134,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof188 : Ban 30 5 s192 := viaSmall (by decide +kernel) (by decide)
def f135 : ℕ := 0xfffefabfffffff
def s193 : List ℕ := [f0,f1,f2,f3,f4,f135]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof189 : Ban 30 5 s193 := viaSmall (by decide +kernel) (by decide)
def f136 : ℕ := 0x14960000001c00
def s194 : List ℕ := [f0,f1,f136,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof190 : Ban 30 5 s194 := viaSmall (by decide +kernel) (by decide)
def f137 : ℕ := 0x248fabc0003ff
def s195 : List ℕ := [f137,f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof191 : Ban 30 5 s195 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof170 : Ban 30 6 s173 := viaBranch (ws := [s66,s174,s103,s175,s176,s178,s179,s180,s181,s182,s69,s183,s184,s185,s106,s186,s187,s188,s189,s190,s191,s192,s193,s194,s195])
  (consBan proof59 (consBan proof171 (consBan proof97 (consBan proof172 (consBan proof173 (consBan proof174 (consBan proof175 (consBan proof176 (consBan proof177 (consBan proof178 (consBan proof62 (consBan proof179 (consBan proof180 (consBan proof181 (consBan proof100 (consBan proof182 (consBan proof183 (consBan proof184 (consBan proof185 (consBan proof186 (consBan proof187 (consBan proof188 (consBan proof189 (consBan proof190 (consBan proof191 (nilBan _ _))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof192 : Ban 30 6 s188 := viaWeakCut rho4 w0 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof193 : Ban 30 6 s189 := viaWeakCut rho3 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s196 : List ℕ := [f38,f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof194 : Ban 30 6 s196 := viaWeakCut rho8 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f138 : ℕ := 0xffbfa47ffffe93
def s197 : List ℕ := [f0,f1,f2,f3,f4,f138]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof195 : Ban 30 6 s197 := viaWeakCut rho4 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s198 : List ℕ := [f0,f1,f2,f3,f39,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof196 : Ban 30 6 s198 := viaWeakCut rho8 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f139 : ℕ := 0x209a47c000293
def s199 : List ℕ := [f139,f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof197 : Ban 30 6 s199 := viaWeakCut rho4 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s200 : List ℕ := [f0,f40,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof198 : Ban 30 6 s200 := viaWeakCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f140 : ℕ := 0xfff7c503ffff1c
def s201 : List ℕ := [f0,f1,f2,f3,f4,f140]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof199 : Ban 30 6 s201 := viaWeakCut rho4 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s202 : List ℕ := [f0,f1,f2,f3,f41,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof200 : Ban 30 6 s202 := viaWeakCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f141 : ℕ := 0x241c50000031c
def s203 : List ℕ := [f141,f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof201 : Ban 30 6 s203 := viaWeakCut rho4 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s204 : List ℕ := [f0,f1,f71,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof202 : Ban 30 6 s204 := viaWeakCut rho3 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f142 : ℕ := 0xfffee803ffffe0
def s205 : List ℕ := [f0,f1,f2,f3,f4,f142]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof203 : Ban 30 6 s205 := viaWeakCut rho4 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s206 : List ℕ := [f0,f1,f2,f3,f72,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof204 : Ban 30 6 s206 := viaWeakCut rho3 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f143 : ℕ := 0x248e8000003e0
def s207 : List ℕ := [f143,f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof205 : Ban 30 6 s207 := viaWeakCut rho4 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f144 : ℕ := 0xa8000003f00000
def s208 : List ℕ := [f0,f1,f2,f144,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof206 : Ban 30 6 s208 := viaWeakCut rho4 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s209 : List ℕ := [f0,f1,f2,f3,f52]
def rho17 : Weak 30 15 := signedPick 1 [1,3,6,11,12,14,15,17,18,20,21,22,23,24,25] (by decide) (by decide) (by decide)
def f145 : ℕ := 0x448199a
def f146 : ℕ := 0x10a061e4
def f147 : ℕ := 0x15fc01f8
def f148 : ℕ := 0x3eebf986
def s210 : List ℕ := [f145,f146,f147,f148]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w15 : Wide 15 5 s210 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof207 : Ban 30 6 s209 := viaWeakCut rho17 w15 (by decide) (by decide +kernel) (by decide +kernel)
def s211 : List ℕ := [f0,f1,f2,f3,f4,f52]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof208 : Ban 30 6 s211 := viaWeakCut rho4 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s212 : List ℕ := [f0,f1,f2,f56,f3]
def s213 : List ℕ := [f5,f0,f1,f2,f56,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof210 : Ban 30 5 s213 := viaSmall (by decide +kernel) (by decide)
def s214 : List ℕ := [f0,f13,f1,f2,f56,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof211 : Ban 30 5 s214 := viaSmall (by decide +kernel) (by decide)
def s215 : List ℕ := [f14,f0,f1,f2,f56,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof212 : Ban 30 5 s215 := viaSmall (by decide +kernel) (by decide)
def s216 : List ℕ := [f57,f0,f1,f2,f56,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof213 : Ban 30 5 s216 := viaSmall (by decide +kernel) (by decide)
def s217 : List ℕ := [f0,f1,f60,f2,f56,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof214 : Ban 30 5 s217 := viaSmall (by decide +kernel) (by decide)
def s218 : List ℕ := [f21,f0,f1,f2,f56,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof215 : Ban 30 5 s218 := viaSmall (by decide +kernel) (by decide)
def s219 : List ℕ := [f77,f0,f1,f2,f56,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof216 : Ban 30 5 s219 := viaSmall (by decide +kernel) (by decide)
def s220 : List ℕ := [f0,f1,f61,f2,f56,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof217 : Ban 30 5 s220 := viaSmall (by decide +kernel) (by decide)
def s221 : List ℕ := [f0,f25,f1,f2,f56,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof218 : Ban 30 5 s221 := viaSmall (by decide +kernel) (by decide)
def f149 : ℕ := 0x412000008fc00
def s222 : List ℕ := [f149,f0,f1,f2,f56,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof219 : Ban 30 5 s222 := viaSmall (by decide +kernel) (by decide)
def f150 : ℕ := 0x57bfa47c3ffe93
def s223 : List ℕ := [f0,f1,f2,f56,f150,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof220 : Ban 30 5 s223 := viaSmall (by decide +kernel) (by decide)
def s224 : List ℕ := [f0,f1,f2,f108,f56,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof221 : Ban 30 5 s224 := viaSmall (by decide +kernel) (by decide)
def f151 : ℕ := 0x209a47c300293
def s225 : List ℕ := [f151,f0,f1,f2,f56,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof222 : Ban 30 5 s225 := viaSmall (by decide +kernel) (by decide)
def f152 : ℕ := 0x108400000f1c00
def s226 : List ℕ := [f0,f152,f1,f2,f56,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof223 : Ban 30 5 s226 := viaSmall (by decide +kernel) (by decide)
def f153 : ℕ := 0x57f7c500cfff1c
def s227 : List ℕ := [f0,f1,f2,f56,f153,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof224 : Ban 30 5 s227 := viaSmall (by decide +kernel) (by decide)
def s228 : List ℕ := [f0,f1,f2,f122,f56,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof225 : Ban 30 5 s228 := viaSmall (by decide +kernel) (by decide)
def f154 : ℕ := 0x241c500c0031c
def s229 : List ℕ := [f154,f0,f1,f2,f56,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof226 : Ban 30 5 s229 := viaSmall (by decide +kernel) (by decide)
def f155 : ℕ := 0x412000000fe000
def s230 : List ℕ := [f0,f1,f155,f2,f56,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof227 : Ban 30 5 s230 := viaSmall (by decide +kernel) (by decide)
def f156 : ℕ := 0x57fee8030fffe0
def s231 : List ℕ := [f0,f1,f2,f56,f156,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof228 : Ban 30 5 s231 := viaSmall (by decide +kernel) (by decide)
def s232 : List ℕ := [f0,f1,f136,f2,f56,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof229 : Ban 30 5 s232 := viaSmall (by decide +kernel) (by decide)
def f157 : ℕ := 0x248e8030003e0
def s233 : List ℕ := [f157,f0,f1,f2,f56,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof230 : Ban 30 5 s233 := viaSmall (by decide +kernel) (by decide)
def s234 : List ℕ := [f95,f0,f1,f2,f56,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof231 : Ban 30 5 s234 := viaSmall (by decide +kernel) (by decide)
def s235 : List ℕ := [f0,f1,f2,f56,f99,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof232 : Ban 30 5 s235 := viaSmall (by decide +kernel) (by decide)
def s236 : List ℕ := [f31,f0,f1,f2,f56,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof233 : Ban 30 5 s236 := viaSmall (by decide +kernel) (by decide)
def s237 : List ℕ := [f110,f0,f1,f2,f56,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof234 : Ban 30 5 s237 := viaSmall (by decide +kernel) (by decide)
def s238 : List ℕ := [f0,f1,f2,f56,f113,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof235 : Ban 30 5 s238 := viaSmall (by decide +kernel) (by decide)
def s239 : List ℕ := [f0,f33,f1,f2,f56,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof236 : Ban 30 5 s239 := viaSmall (by decide +kernel) (by decide)
def s240 : List ℕ := [f124,f0,f1,f2,f56,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof237 : Ban 30 5 s240 := viaSmall (by decide +kernel) (by decide)
def s241 : List ℕ := [f0,f1,f2,f56,f127,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof238 : Ban 30 5 s241 := viaSmall (by decide +kernel) (by decide)
def s242 : List ℕ := [f0,f1,f66,f2,f56,f3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof239 : Ban 30 5 s242 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof240 : Ban 30 5 s209 := viaWeakCut rho4 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s243 : List ℕ := [f0,f1,f2,f56,f52]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof241 : Ban 30 5 s243 := viaWeakCut rho4 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s244 : List ℕ := [f0,f1,f2,f56,f3,f52]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof242 : Ban 30 5 s244 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof209 : Ban 30 6 s212 := viaBranch (ws := [s213,s46,s214,s215,s216,s85,s217,s218,s219,s123,s220,s221,s222,s223,s224,s225,s226,s227,s228,s229,s230,s231,s232,s233,s234,s143,s235,s236,s237,s167,s238,s239,s240,s191,s241,s242,s209,s243,s244])
  (consBan proof210 (consBan proof39 (consBan proof211 (consBan proof212 (consBan proof213 (consBan proof78 (consBan proof214 (consBan proof215 (consBan proof216 (consBan proof116 (consBan proof217 (consBan proof218 (consBan proof219 (consBan proof220 (consBan proof221 (consBan proof222 (consBan proof223 (consBan proof224 (consBan proof225 (consBan proof226 (consBan proof227 (consBan proof228 (consBan proof229 (consBan proof230 (consBan proof231 (consBan proof137 (consBan proof232 (consBan proof233 (consBan proof234 (consBan proof162 (consBan proof235 (consBan proof236 (consBan proof237 (consBan proof187 (consBan proof238 (consBan proof239 (consBan proof240 (consBan proof241 (consBan proof242 (nilBan _ _))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def s245 : List ℕ := [f0,f1,f2,f56,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof243 : Ban 30 6 s245 := viaWeakCut rho4 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f158 : ℕ := 0x12bc0003ff
def s246 : List ℕ := [f158,f0,f1,f2,f3,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof244 : Ban 30 6 s246 := viaWeakCut rho4 w0 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof0 : Ban 30 7 s0 := viaBranch (ws := [s1,s3,s10,s11,s47,s48,s59,s63,s86,s87,s99,s100,s124,s125,s134,s141,s148,s149,s161,s165,s172,s173,s188,s189,s196,s197,s198,s199,s200,s201,s202,s203,s204,s205,s206,s207,s208,s209,s211,s212,s245,s246])
  (consBan proof1 (consBan proof2 (consBan proof40 (consBan proof41 (consBan proof42 (consBan proof43 (consBan proof79 (consBan proof80 (consBan proof81 (consBan proof82 (consBan proof117 (consBan proof118 (consBan proof119 (consBan proof120 (consBan proof142 (consBan proof143 (consBan proof144 (consBan proof145 (consBan proof167 (consBan proof168 (consBan proof169 (consBan proof170 (consBan proof192 (consBan proof193 (consBan proof194 (consBan proof195 (consBan proof196 (consBan proof197 (consBan proof198 (consBan proof199 (consBan proof200 (consBan proof201 (consBan proof202 (consBan proof203 (consBan proof204 (consBan proof205 (consBan proof206 (consBan proof207 (consBan proof208 (consBan proof209 (consBan proof243 (consBan proof244 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
theorem cert6 : Ban 30 7 s0 := proof0
end PEqualNP.Outside.L_meta_12325.B1

namespace PEqualNP.Outside.L_meta_12325
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def target (x : Fin 6 → Bool) := Nat.testBit (4276682240 * 2 ^ 32 + 4276676608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def witness : Circuit := ⟨[⟨.or,[0,1]⟩,⟨.and,[0,1]⟩,⟨.and,[6,2]⟩,⟨.or,[7,8]⟩,⟨.or,[6,2]⟩,⟨.or,[3,4]⟩,⟨.and,[9,11]⟩,⟨.or,[4,5]⟩,⟨.and,[3,13]⟩,⟨.and,[10,14]⟩,⟨.or,[12,15]⟩],16⟩
theorem shaped : Monotone2 witness := by simp [witness,Monotone2]
theorem cost : witness.size=11 := rfl
theorem valid : ∀ x, witness.eval (List.ofFn x)=target x := by decide +kernel
def bank0 : List ℕ := [0xe1b86e078fe3f,0x62c5b1638f1fc7,0x30368da1c0fe3f8,0x5b4006dbff003ff,0x6d9b6001ffffc00]
theorem wide0 : Wide 30 7 bank0 := widen (by decide +kernel) B0.cert6
def bank1 : List ℕ := [0x61ba47c38fe93,0x12c5c500cf1f1c,0x4368e8030fe3e0,0xa80012bff003ff,0xfdb60003fffc00]
theorem wide1 : Wide 30 7 bank1 := widen (by decide +kernel) B1.cert6
def inputs : List ℕ := [0x200c37488070dc37f0e3fa4e078fe3f,0x258b8a03162d8a033c7c7238f1fc7,0x86d1d0181b46d00c3f8f81c0fe3f8,0x215000252da0036dffc00fffff003ff,0x1fb6c0036cdb0000ffff001ffffc00,0x1fffffff80000001fffffffc0000000]
def v : ℕ := 0x1fffffff80000001fffffffc0000000
def rr0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29]
def ix0 := rr0 ++ rr0.map (61+·)
def base0 : ℕ := 90
def pr0 : Weak 61 30 := signedPick base0 rr0 (by decide) (by decide) (by decide)
theorem images0 : ∀ a∈inputs, pr0.f a=0 ∨ pr0.f a∈bank0 := by decide +kernel
def rr1 : List ℕ := [30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59]
def ix1 := rr1 ++ rr1.map (61+·)
def base1 : ℕ := 120
def pr1 : Weak 61 30 := signedPick base1 rr1 (by decide) (by decide) (by decide)
theorem images1 : ∀ a∈inputs, pr1.f a=0 ∨ pr1.f a∈bank1 := by decide +kernel
def pr : Bool → Weak 61 30 | false => pr0 | true => pr1
def posBits : ℕ := 0x29a69a69f3cebae79df6db6d75d73cf3beeb6cb2baaaa692dc71c69a6996595d65965555534d33ce38e34d34b2cb
def negBits : ℕ := 0x9820820e34e32e319f4ca6d31972c639e6968923a22a2101850c6122984491d44865111524431cc28630914a243
def sample (bank : ℕ) (i : Fin 61) (j : Fin 6) := bank.testBit (6*i.val+j.val)

def seeds : List Wire := inputs.map (fun a => (false,a))
set_option maxHeartbeats 1000000 in
theorem listed : ∀ i : Fin 61, seeds.map (read i.val)=List.ofFn (sample posBits i) ∧
    seeds.map (read (61+i.val))=List.ofFn (sample negBits i) := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem labels : ∀ i : Fin 61, target (sample posBits i)=true ∧ target (sample negBits i)=false := by decide +kernel
theorem essential : ∀ a∈inputs, ∃ i : Fin 61, ∀ b∈inputs, b.testBit i.val≠b.testBit (61+i.val) → b=a := by decide +kernel
theorem initial {k S} (live : Live 61 k S) (sub : ∀ a∈S,a∈inputs) : S=inputs.toFinset := by
  apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
  intro a ha
  obtain ⟨i,h⟩ := essential a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
  exact h b (sub b hb) sep ▸ hb
theorem trace (C : Circuit) (fan : FanInTwo C) (eq : circuitFun 6 C=target) :
    ∃ k≤C.gates.countP counted, Live 61 k inputs.toFinset := by
  let final := execute C.gates seeds
  let out := final.getD C.output zero
  have ev (i : ℕ) : read i out = C.eval (seeds.map (read i)) := by
    rw [show read i out = (final.map (read i)).getD C.output false from (read_get i final C.output).symm]
    rw [show final=execute C.gates seeds from rfl,execute_read i _ _ fan];rfl
  have result (x : Fin 6 → Bool) : C.eval (List.ofFn x)=target x := congrFun eq x
  have good : Good 61 out.2 := by
    intro i hi same
    let j : Fin 61 := ⟨i,hi⟩
    have diff : read i out=read (61+i) out := by simp [read,same]
    have p := ev i;have n := ev (61+i)
    rw [(listed j).1,result,(labels j).1] at p
    rw [(listed j).2,result,(labels j).2] at n
    rw [p,n] at diff;contradiction
  have nz : out.2≠0 := by
    intro z;have bad := good 0 (by decide);simp [z] at bad
  have found : out.2∈ reps final := (get_simple final C.output).resolve_left nz
  obtain ⟨k,S,limit,live,sub⟩ := extract good nz C.gates seeds found
  have stays : ∀ a∈S, a∈inputs := by simpa [reps,seeds,List.map_map,Function.comp_def] using sub
  exact ⟨k,limit,initial live stays ▸ live⟩


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

theorem ten {k : ℕ} (live : Live 61 k inputs.toFinset) : 10≤k := by
  obtain ⟨t,j,T,lim,ok,sub⟩ := doubleElim pr v killed (by decide +kernel) live (by decide)
  by_contra! small
  have project {w : List ℕ} (im : ∀ a∈inputs, (pr t).f a=0 ∨ (pr t).f a∈w) : Possible 30 7 w := by
    refine ⟨j,T,by omega,ok,?_⟩
    intro x hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp (sub x hx)
    exact (im _ (List.mem_toFinset.mp ha)).resolve_left (liveNonzero ok _ hx)
  cases t
  · exact wide0 (project images0)
  · exact wide1 (project images1)

theorem counted_lt {gs : List Gate} (h : ∃ g ∈ gs, g.op = .not) : gs.countP counted < gs.length := by
  apply Nat.lt_of_le_of_ne List.countP_le_length
  intro eq
  obtain ⟨g,hg,hop⟩ := h
  have bad := List.countP_eq_length.mp eq g hg
  simp [counted,hop] at bad

theorem noSaving (s : ℕ) (h : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x,C.eval (List.ofFn x)=target x := by
  obtain ⟨C,fan,hsize,ev⟩ := h
  by_cases used : ∃ g∈C.gates, g.op=.not
  · obtain ⟨k,lim,ok⟩ := trace C fan (funext ev)
    have lb := ten ok
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
end PEqualNP.Outside.L_meta_12325

theorem PEqualNP.Outside.L_meta_12325 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276682240 * 2 ^ 32 + 4276676608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276682240 * 2 ^ 32 + 4276676608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := PEqualNP.Outside.L_meta_12325.noSaving
