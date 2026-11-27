import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_11407


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

namespace Travail11408
open M10720
def sixBase : List ℕ := [0xa00a00a00a00a00a00a00a00a00a000000000fff000fff000fff000fff,0x10c10c10c10c10c10c10c10c10c10c000000fff000000000fff000fff000,0x50050050050050050050050050050000fff000000fff000000000ffffff,0x260260260260260260260260260260fff000000000000000ffffff000000,0xb80b80b80b80b80b80b80b80b80b80000000000000ffffff000000000000,0xc00c00c00c00c00c00c00c00c00c00ffffffffffff000000000000000000]
def septBase : List ℕ := [0x14014014014014014014014014014000000000fff000fff000fff000fff,0x218218218218218218218218218218000000fff000000000fff000fff000,0x1000000000000000000000000000000,0xa00a00a00a00a00a00a00a00a00a0000fff000000fff000000000ffffff,0x4c04c04c04c04c04c04c04c04c04c0fff000000000000000ffffff000000,0x3701701701701701701701701701701000000000000ffffff000000000000,0x1801801801801801801801801801800ffffffffffff000000000000000000]
def posBits : ℕ := 0x24a142850a142850a142850912244891224489122448850a142850a142850a14283060c183060c183060c150a142850a142850a142842850a142850a142850a1244891224489122448912224489122448912244891142850a142850a142850a122448912244891224489
def negBits : ℕ := 0x20c10182240608080608080c10182240608080608080c10182240608080608080c10182240608080608080c10182240608080608080c10182240608080608080c10182240608080608080c10182240608080608080c10182240608080608080c10182240608080608080
end Travail11408

namespace Travail11408
open M10720
def w0 : ℕ := 0xa00a00a00a00a00a00a00a00a00a000000000fff000fff000fff000fff

def w1 : ℕ := 0x50050050050050050050050050050000fff000000fff000000000ffffff

def w2 : ℕ := 0x10c10c10c10c10c10c10c10c10c10c000000fff000000000fff000fff000

def w3 : ℕ := 0x260260260260260260260260260260fff000000000000000ffffff000000

def w4 : ℕ := 0xb80b80b80b80b80b80b80b80b80b80000000000000ffffff000000000000

def w5 : ℕ := 0xc00c00c00c00c00c00c00c00c00c00ffffffffffff000000000000000000

def v0 : List ℕ := [w0,w1,w2,w3,w4,w5]

def w6 : ℕ := 0xfff

def v1 : List ℕ := [w6,w0,w1,w2,w3,w4,w5]

def w7 : ℕ := 0x4004000000000000000004000fffbeaffffffffffffffffffffffff

def w8 : ℕ := 0x10010000000000000000010000ffffffbeafffffffffffffffffffff

def w9 : ℕ := 0x400400000000000000000400000000415415000000000000000000000

def v2 : List ℕ := [w7,w8,w9]

theorem h2 : Ban 120 3 v2 := viaSmall (by decide +kernel) (by decide)

def p74 : Projection 120 120 := pinchProj 120 0x415415000000000000000415000 12 (by decide) (by decide)

theorem minorant74 : Wide 120 3 v2 := widen (by decide +kernel) h2

theorem h1 : Ban 120 7 v1 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w10 : ℕ := 0xfff000

def v3 : List ℕ := [w10,w0,w1,w2,w3,w4,w5]

def w11 : ℕ := 0x2002000000000002fffffffffffff6cfffffffffffffff

def w12 : ℕ := 0x10010000000000010ffffffffffffffff6cffffffffffff

def w13 : ℕ := 0x80080000000000080000000000000093093000000000000

def v4 : List ℕ := [w11,w12,w13]

theorem h4 : Ban 120 3 v4 := viaSmall (by decide +kernel) (by decide)

def p41 : Projection 120 120 := pinchProj 120 0x93093000000000093 0 (by decide) (by decide)

theorem minorant41 : Wide 120 3 v4 := widen (by decide +kernel) h4

theorem h3 : Ban 120 7 v3 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w14 : ℕ := 0xfff000000

def v5 : List ℕ := [w14,w0,w1,w2,w3,w4,w5]

theorem h5 : Ban 120 7 v5 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w15 : ℕ := 0xfff000000000

def v6 : List ℕ := [w15,w0,w1,w2,w3,w4,w5]

theorem h6 : Ban 120 7 v6 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w16 : ℕ := 0xfff000000000000

def v7 : List ℕ := [w16,w0,w1,w2,w3,w4,w5]

def w17 : ℕ := 0x2000002000000000000000002fffbecffffffffffffffffffffffff

def w18 : ℕ := 0x10000010000000000000000010fffffffffbecffffffffffffffffff

def w19 : ℕ := 0x400000400000000000000000400000413000413000000000000000000

def v8 : List ℕ := [w17,w18,w19]

theorem h8 : Ban 120 3 v8 := viaSmall (by decide +kernel) (by decide)

def p73 : Projection 120 120 := pinchProj 120 0x413000413000000000000000413 0 (by decide) (by decide)

theorem minorant73 : Wide 120 3 v8 := widen (by decide +kernel) h8

theorem h7 : Ban 120 7 v7 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w20 : ℕ := 0xfff000000000000000

def v9 : List ℕ := [w20,w0,w1,w2,w3,w4,w5]

theorem h9 : Ban 120 7 v9 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w21 : ℕ := 0xfff000000000000000000

def v10 : List ℕ := [w21,w0,w1,w2,w3,w4,w5]

theorem h10 : Ban 120 7 v10 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w22 : ℕ := 0xfff000000000000000000000

def v11 : List ℕ := [w22,w0,w1,w2,w3,w4,w5]

theorem h11 : Ban 120 7 v11 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w23 : ℕ := 0xfff000000000000000000000000

def v12 : List ℕ := [w23,w0,w1,w2,w3,w4,w5]

theorem h12 : Ban 120 7 v12 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w24 : ℕ := 0xfff000000000000000000000000000

def v13 : List ℕ := [w24,w0,w1,w2,w3,w4,w5]

theorem h13 : Ban 120 7 v13 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w25 : ℕ := 0x2002002002002002002002002002000000000fff000fff000fff000fff

def v14 : List ℕ := [w25,w0,w1,w2,w3,w4,w5]

theorem h14 : Ban 120 7 v14 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v15 : List ℕ := [w25,w1,w2,w3,w4,w5]

def w26 : ℕ := 0x200200000200200200000200000210c10cffffff10cfffffffffffffff

def w27 : ℕ := 0x5005000005005005000005000005010cffffff10cfff10cfff10cffffff

def w28 : ℕ := 0x260260000260260260000260000260ef3000000000000000000ef3000000

def w29 : ℕ := 0xa80a80000a80a80a80000a80000a80000000000000ef3ef3000000000000

def w30 : ℕ := 0xc00c00000c00c00c00000c00000c00ef3ef3000ef3000000000000000000

def v16 : List ℕ := [w26,w27,w28,w29,w30]

def w31 : ℕ := 0xef3000000

def v17 : List ℕ := [w31,w26,w27,w28,w29,w30]

theorem h17 : Ban 120 5 v17 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w32 : ℕ := 0xef3000000000000

def v18 : List ℕ := [w32,w26,w27,w28,w29,w30]

theorem h18 : Ban 120 5 v18 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w33 : ℕ := 0xef3000000000000000

def v19 : List ℕ := [w33,w26,w27,w28,w29,w30]

theorem h19 : Ban 120 5 v19 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w34 : ℕ := 0xef3000000000000000000

def v20 : List ℕ := [w34,w26,w27,w28,w29,w30]

theorem h20 : Ban 120 5 v20 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w35 : ℕ := 0xef3000000000000000000000000

def v21 : List ℕ := [w35,w26,w27,w28,w29,w30]

theorem h21 : Ban 120 5 v21 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w36 : ℕ := 0x10c10cfff10c10c10cfff10cffffff

def v22 : List ℕ := [w36,w26,w27,w28,w29,w30]

def w37 : ℕ := 0x2000000002000000000002000000bdcfffffffffffffffffffffffffff

def w38 : ℕ := 0x20000000020000000000020000000fffffffffbdcffffffffffffffffff

def w39 : ℕ := 0x400000000400000000000400000000423000000423000000000000000000

def v23 : List ℕ := [w37,w38,w39]

theorem h23 : Ban 120 3 v23 := viaSmall (by decide +kernel) (by decide)

def p81 : Projection 120 120 := pinchProj 120 0x423000000423000000000423000000 24 (by decide) (by decide)

theorem minorant81 : Wide 120 3 v23 := widen (by decide +kernel) h23

theorem h22 : Ban 120 5 v22 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def w40 : ℕ := 0xef3000000000000000000000000000

def v24 : List ℕ := [w40,w26,w27,w28,w29,w30]

theorem h24 : Ban 120 5 v24 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w41 : ℕ := 0x2002000002002002000002000002000000000ef3000ef3000ef3000000

def v25 : List ℕ := [w41,w26,w27,w28,w29,w30]

theorem h25 : Ban 120 5 v25 := viaSmall (by decide +kernel) (by decide)

def w42 : ℕ := 0x200200000200200200000200000210c10cfff10c10cfffffffffffffff

def v26 : List ℕ := [w42,w26,w27,w28,w29,w30]

theorem h26 : Ban 120 5 v26 := viaSmall (by decide +kernel) (by decide)

def w43 : ℕ := 0x200200000200200200000200000210c10cffffff10c10cffffffffffff

def v27 : List ℕ := [w43,w26,w27,w28,w29,w30]

theorem h27 : Ban 120 5 v27 := viaSmall (by decide +kernel) (by decide)

def w44 : ℕ := 0x200200000200200200000200000210c10cffffff10cffffff10cffffff

def v28 : List ℕ := [w44,w26,w27,w28,w29,w30]

theorem h28 : Ban 120 5 v28 := viaSmall (by decide +kernel) (by decide)

def w45 : ℕ := 0x1001000001001001000001000001010cffffff10cfff10cfff10cffffff

def v29 : List ℕ := [w26,w45,w27,w28,w29,w30]

theorem h29 : Ban 120 5 v29 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v30 : List ℕ := [w26,w45,w28,w29,w30]

theorem h30 : Ban 120 5 v30 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w46 : ℕ := 0x40040000040040040000040000040000000000000000000000000000000

def v31 : List ℕ := [w26,w46,w27,w28,w29,w30]

theorem h31 : Ban 120 5 v31 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w47 : ℕ := 0x50050000050050050000050000050000ef3000000ef3000000000000000

def v32 : List ℕ := [w26,w47,w27,w28,w29,w30]

theorem h32 : Ban 120 5 v32 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def w48 : ℕ := 0x5005000005005005000005000005010c10cfff10cfff10cfff10cffffff

def v33 : List ℕ := [w26,w48,w27,w28,w29,w30]

theorem h33 : Ban 120 5 v33 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w49 : ℕ := 0x5005000005005005000005000005010cffffff10c10c10cfff10cffffff

def v34 : List ℕ := [w26,w49,w27,w28,w29,w30]

theorem h34 : Ban 120 5 v34 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w50 : ℕ := 0x5205200005205205200005200005210cfffffffffffffffffffffffffff

def v35 : List ℕ := [w26,w27,w50,w28,w29,w30]

theorem h35 : Ban 120 5 v35 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def w51 : ℕ := 0x60060000060060060000060000060ef3000000000000000000ef3000000

def v36 : List ℕ := [w26,w27,w51,w28,w29,w30]

theorem h36 : Ban 120 5 v36 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v37 : List ℕ := [w26,w27,w51,w29,w30]

theorem h37 : Ban 120 5 v37 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w52 : ℕ := 0x200200000200200200000200000200000000000000000000000000000000

def v38 : List ℕ := [w26,w27,w52,w28,w29,w30]

theorem h38 : Ban 120 5 v38 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w53 : ℕ := 0x220220000220220220000220000220ef3000000000000000000ef3000000

def v39 : List ℕ := [w26,w27,w53,w28,w29,w30]

theorem h39 : Ban 120 5 v39 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v40 : List ℕ := [w26,w27,w53,w29,w30]

theorem h40 : Ban 120 5 v40 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w54 : ℕ := 0x260260000260260260000260000260000000000000000000000ef3000000

def v41 : List ℕ := [w26,w27,w54,w28,w29,w30]

theorem h41 : Ban 120 5 v41 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w55 : ℕ := 0x260260000260260260000260000260ef3000000000000000000000000000

def v42 : List ℕ := [w26,w27,w55,w28,w29,w30]

theorem h42 : Ban 120 5 v42 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w56 : ℕ := 0x262262000262262262000262000262fff10cffffff10cfffffffffffffff

def v43 : List ℕ := [w26,w27,w28,w56,w29,w30]

theorem h43 : Ban 120 5 v43 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w57 : ℕ := 0x270270000270270270000270000270fffffffff10cfff10cffffffffffff

def v44 : List ℕ := [w26,w27,w28,w57,w29,w30]

theorem h44 : Ban 120 5 v44 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w58 : ℕ := 0x280280000280280280000280000280000000000000ef3ef3000000000000

def v45 : List ℕ := [w26,w27,w28,w58,w29,w30]

theorem h45 : Ban 120 5 v45 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v46 : List ℕ := [w26,w27,w28,w58,w30]

theorem h46 : Ban 120 5 v46 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w59 : ℕ := 0x400400000400400400000400000400ef3ef3000ef3000000000000000000

def v47 : List ℕ := [w26,w27,w28,w59,w29]

theorem h47 : Ban 120 5 v47 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v48 : List ℕ := [w26,w27,w28,w59,w29,w30]

theorem h48 : Ban 120 5 v48 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w60 : ℕ := 0x800800000800800800000800000800000000000000000000000000000000

def v49 : List ℕ := [w26,w27,w28,w60,w29,w30]

theorem h49 : Ban 120 5 v49 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w61 : ℕ := 0x880880000880880880000880000880000000000000ef3ef3000000000000

def v50 : List ℕ := [w26,w27,w28,w61,w29,w30]

theorem h50 : Ban 120 5 v50 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v51 : List ℕ := [w26,w27,w28,w61,w30]

theorem h51 : Ban 120 5 v51 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w62 : ℕ := 0xa80a80000a80a80a80000a80000a80000000000000000ef3000000000000

def v52 : List ℕ := [w26,w27,w28,w62,w29,w30]

theorem h52 : Ban 120 5 v52 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w63 : ℕ := 0xa80a80000a80a80a80000a80000a80000000000000ef3000000000000000

def v53 : List ℕ := [w26,w27,w28,w63,w29,w30]

theorem h53 : Ban 120 5 v53 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w64 : ℕ := 0xa82a82000a82a82a82000a82000a8210c10cffffffffffffffffffffffff

def v54 : List ℕ := [w26,w27,w28,w29,w64,w30]

theorem h54 : Ban 120 5 v54 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w65 : ℕ := 0xad0ad0000ad0ad0ad0000ad0000ad010cffffff10cfffffffff10cffffff

def v55 : List ℕ := [w26,w27,w28,w29,w65,w30]

theorem h55 : Ban 120 5 v55 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w66 : ℕ := 0xae0ae0000ae0ae0ae0000ae0000ae0ef3000000000ef3ef3000ef3000000

def v56 : List ℕ := [w26,w27,w28,w29,w66,w30]

theorem h56 : Ban 120 5 v56 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w67 : ℕ := 0xc00c00000c00c00c00000c00000c00000ef3000ef3000000000000000000

def v57 : List ℕ := [w26,w27,w28,w29,w67,w30]

theorem h57 : Ban 120 5 v57 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w68 : ℕ := 0xc00c00000c00c00c00000c00000c00ef3000000ef3000000000000000000

def v58 : List ℕ := [w26,w27,w28,w29,w68,w30]

theorem h58 : Ban 120 5 v58 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w69 : ℕ := 0xc00c00000c00c00c00000c00000c00ef3ef3000000000000000000000000

def v59 : List ℕ := [w26,w27,w28,w29,w69,w30]

theorem h59 : Ban 120 5 v59 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w70 : ℕ := 0xc02c02000c02c02c02000c02000c02ffffffffffff10cfffffffffffffff

def v60 : List ℕ := [w26,w27,w28,w29,w30,w70]

theorem h60 : Ban 120 5 v60 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w71 : ℕ := 0xc50c50000c50c50c50000c50000c50fffffffffffffff10cfff10cffffff

def v61 : List ℕ := [w26,w27,w28,w29,w30,w71]

theorem h61 : Ban 120 5 v61 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w72 : ℕ := 0xe60e60000e60e60e60000e60000e60ef3ef3000ef3000000000ef3000000

def v62 : List ℕ := [w26,w27,w28,w29,w30,w72]

theorem h62 : Ban 120 5 v62 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w73 : ℕ := 0xe80e80000e80e80e80000e80000e80ef3ef3000ef3ef3ef3000000000000

def v63 : List ℕ := [w26,w27,w28,w29,w30,w73]

theorem h63 : Ban 120 5 v63 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v64 : List ℕ := [w26,w27,w28,w29,w73]

theorem h64 : Ban 120 5 v64 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v65 : List ℕ := [w26,w27,w28,w66,w30]

theorem h65 : Ban 120 5 v65 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v66 : List ℕ := [w26,w27,w28,w30,w73]

theorem h66 : Ban 120 5 v66 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v67 : List ℕ := [w26,w27,w57,w29,w30]

theorem h67 : Ban 120 5 v67 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v68 : List ℕ := [w26,w27,w29,w66,w30]

theorem h68 : Ban 120 5 v68 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v69 : List ℕ := [w26,w28,w57,w29,w30]

theorem h69 : Ban 120 5 v69 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h16 : Ban 120 6 v16 := viaBranch (ws := [v17,v18,v19,v20,v21,v22,v24,v25,v26,v27,v28,v29,v30,v31,v32,v33,v34,v35,v36,v37,v38,v39,v40,v41,v42,v43,v44,v45,v46,v47,v48,v49,v50,v51,v52,v53,v54,v55,v56,v57,v58,v59,v60,v61,v62,v63,v64,v65,v66,v67,v68,v69])
  (consBan h17 (consBan h18 (consBan h19 (consBan h20 (consBan h21 (consBan h22 (consBan h24 (consBan h25 (consBan h26 (consBan h27 (consBan h28 (consBan h29 (consBan h30 (consBan h31 (consBan h32 (consBan h33 (consBan h34 (consBan h35 (consBan h36 (consBan h37 (consBan h38 (consBan h39 (consBan h40 (consBan h41 (consBan h42 (consBan h43 (consBan h44 (consBan h45 (consBan h46 (consBan h47 (consBan h48 (consBan h49 (consBan h50 (consBan h51 (consBan h52 (consBan h53 (consBan h54 (consBan h55 (consBan h56 (consBan h57 (consBan h58 (consBan h59 (consBan h60 (consBan h61 (consBan h62 (consBan h63 (consBan h64 (consBan h65 (consBan h66 (consBan h67 (consBan h68 (consBan h69 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def p121 : Projection 120 120 := pinchProj 120 0xef3ef3000ef3ef3ef3000ef3000ef3 0 (by decide) (by decide)

theorem minorant121 : Wide 120 6 v16 := widen (by decide +kernel) h16

theorem h15 : Ban 120 7 v15 := cutTest_ok p121 (extra := []) minorant121 (by decide) (by decide +kernel)

def w74 : ℕ := 0x8008008008008008008008008008000000000000000000000000000000

def v70 : List ℕ := [w74,w0,w1,w2,w3,w4,w5]

theorem h70 : Ban 120 7 v70 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w75 : ℕ := 0xa00a00a00a00a00a00a00a00a00a000000000000000fff000fff000fff

def v71 : List ℕ := [w75,w0,w1,w2,w3,w4,w5]

theorem h71 : Ban 120 7 v71 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w76 : ℕ := 0xa00a00a00a00a00a00a00a00a00a000000000fff000000000fff000fff

def v72 : List ℕ := [w76,w0,w1,w2,w3,w4,w5]

theorem h72 : Ban 120 7 v72 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w77 : ℕ := 0xa00a00a00a00a00a00a00a00a00a000000000fff000fff000000000fff

def v73 : List ℕ := [w77,w0,w1,w2,w3,w4,w5]

theorem h73 : Ban 120 7 v73 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w78 : ℕ := 0xa00a00a00a00a00a00a00a00a00a000000000fff000fff000fff000000

def v74 : List ℕ := [w78,w0,w1,w2,w3,w4,w5]

theorem h74 : Ban 120 7 v74 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w79 : ℕ := 0xc00c00c00c00c00c00c00c00c00c000000fff000000000fff000fff000

def v75 : List ℕ := [w0,w79,w1,w2,w3,w4,w5]

theorem h75 : Ban 120 7 v75 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v76 : List ℕ := [w0,w79,w1,w3,w4,w5]

theorem h76 : Ban 120 7 v76 := cutTest_ok p121 (extra := []) minorant121 (by decide) (by decide +kernel)

def w80 : ℕ := 0x10010010010010010010010010010000fff000000fff000000000ffffff

def v77 : List ℕ := [w0,w80,w1,w2,w3,w4,w5]

theorem h77 : Ban 120 7 v77 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v78 : List ℕ := [w0,w80,w2,w3,w4,w5]

def w81 : ℕ := 0xa00a00a00a00a00000000a00afff260260fff260fffffffff260fff

def w82 : ℕ := 0x10010010010010000000010010ffffff260260fff260ffffffffffff

def w83 : ℕ := 0x10c10c10c10c10c00000010c10c000000d9f000000000000000d9f000

def w84 : ℕ := 0x980980980980980000000980980000000000000d9fd9f000000000000

def w85 : ℕ := 0xc00c00c00c00c00000000c00c00000d9fd9fd9f000000000000000000

def v79 : List ℕ := [w81,w82,w83,w84,w85]

def w86 : ℕ := 0xd9f000

def v80 : List ℕ := [w86,w81,w82,w83,w84,w85]

theorem h80 : Ban 120 5 v80 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w87 : ℕ := 0xd9f000000000000

def v81 : List ℕ := [w87,w81,w82,w83,w84,w85]

theorem h81 : Ban 120 5 v81 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w88 : ℕ := 0xd9f000000000000000

def v82 : List ℕ := [w88,w81,w82,w83,w84,w85]

theorem h82 : Ban 120 5 v82 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w89 : ℕ := 0xd9f000000000000000000

def v83 : List ℕ := [w89,w81,w82,w83,w84,w85]

theorem h83 : Ban 120 5 v83 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w90 : ℕ := 0xd9f000000000000000000000

def v84 : List ℕ := [w90,w81,w82,w83,w84,w85]

theorem h84 : Ban 120 5 v84 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w91 : ℕ := 0xd9f000000000000000000000000

def v85 : List ℕ := [w91,w81,w82,w83,w84,w85]

theorem h85 : Ban 120 5 v85 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w92 : ℕ := 0xfff260260260260260ffffff260fff

def v86 : List ℕ := [w92,w81,w82,w83,w84,w85]

theorem h86 : Ban 120 5 v86 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w93 : ℕ := 0x2002002002002000000002002fff260260fff260fffffffff260fff

def v87 : List ℕ := [w93,w81,w82,w83,w84,w85]

theorem h87 : Ban 120 5 v87 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v88 : List ℕ := [w93,w82,w83,w84,w85]

theorem h88 : Ban 120 5 v88 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w94 : ℕ := 0x8008008008008000000008008000000000000000000000000000000

def v89 : List ℕ := [w94,w81,w82,w83,w84,w85]

theorem h89 : Ban 120 5 v89 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w95 : ℕ := 0xa00a00a00a00a00000000a00a000000000d9f000d9f000000000000

def v90 : List ℕ := [w95,w81,w82,w83,w84,w85]

theorem h90 : Ban 120 5 v90 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w96 : ℕ := 0xa00a00a00a00a00000000a00afff260260260260fffffffff260fff

def v91 : List ℕ := [w96,w81,w82,w83,w84,w85]

theorem h91 : Ban 120 5 v91 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w97 : ℕ := 0xa00a00a00a00a00000000a00afff260260fff260260ffffff260fff

def v92 : List ℕ := [w97,w81,w82,w83,w84,w85]

theorem h92 : Ban 120 5 v92 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w98 : ℕ := 0xc00c00c00c00c00000000c00c000000d9f000000000000000d9f000

def v93 : List ℕ := [w81,w98,w82,w83,w84,w85]

theorem h93 : Ban 120 5 v93 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v94 : List ℕ := [w81,w98,w82,w84,w85]

theorem h94 : Ban 120 5 v94 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w99 : ℕ := 0x10010010010010000000010010000d9f000000d9f000000000d9f000

def v95 : List ℕ := [w81,w99,w82,w83,w84,w85]

theorem h95 : Ban 120 5 v95 := viaSmall (by decide +kernel) (by decide)

def w100 : ℕ := 0x10010010010010000000010010fff260260260fff260ffffffffffff

def v96 : List ℕ := [w81,w100,w82,w83,w84,w85]

theorem h96 : Ban 120 5 v96 := viaSmall (by decide +kernel) (by decide)

def w101 : ℕ := 0x10010010010010000000010010ffffff260260260260ffffffffffff

def v97 : List ℕ := [w81,w101,w82,w83,w84,w85]

theorem h97 : Ban 120 5 v97 := viaSmall (by decide +kernel) (by decide)

def w102 : ℕ := 0x10010010010010000000010010ffffff260260fff260ffffff260fff

def v98 : List ℕ := [w81,w102,w82,w83,w84,w85]

theorem h98 : Ban 120 5 v98 := viaSmall (by decide +kernel) (by decide)

def w103 : ℕ := 0x1a01a01a01a01a00000001a01affffff260fffffffffffffffffffff

def v99 : List ℕ := [w81,w82,w103,w83,w84,w85]

theorem h99 : Ban 120 5 v99 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w104 : ℕ := 0x100100100100100000000100100000000000000000000000000000000

def v100 : List ℕ := [w81,w82,w104,w83,w84,w85]

theorem h100 : Ban 120 5 v100 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w105 : ℕ := 0x104104104104104000000104104000000d9f000000000000000d9f000

def v101 : List ℕ := [w81,w82,w105,w83,w84,w85]

theorem h101 : Ban 120 5 v101 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v102 : List ℕ := [w81,w82,w105,w84,w85]

theorem h102 : Ban 120 5 v102 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w106 : ℕ := 0x10c10c10c10c10c00000010c10c000000000000000000000000d9f000

def v103 : List ℕ := [w81,w82,w106,w83,w84,w85]

theorem h103 : Ban 120 5 v103 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w107 : ℕ := 0x10c10c10c10c10c00000010c10c000000d9f000000000000000000000

def v104 : List ℕ := [w81,w82,w107,w83,w84,w85]

theorem h104 : Ban 120 5 v104 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w108 : ℕ := 0x10e10e10e10e10e00000010e10efff260ffffff260fffffffffffffff

def v105 : List ℕ := [w81,w82,w83,w108,w84,w85]

theorem h105 : Ban 120 5 v105 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w109 : ℕ := 0x11c11c11c11c11c00000011c11cfffffffff260fff260ffffffffffff

def v106 : List ℕ := [w81,w82,w83,w109,w84,w85]

theorem h106 : Ban 120 5 v106 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w110 : ℕ := 0x180180180180180000000180180000000000000d9fd9f000000000000

def v107 : List ℕ := [w81,w82,w83,w110,w84,w85]

theorem h107 : Ban 120 5 v107 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v108 : List ℕ := [w81,w82,w83,w110,w85]

theorem h108 : Ban 120 5 v108 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w111 : ℕ := 0x400400400400400000000400400000d9fd9fd9f000000000000000000

def v109 : List ℕ := [w81,w82,w83,w111,w84]

theorem h109 : Ban 120 5 v109 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v110 : List ℕ := [w81,w82,w83,w111,w84,w85]

theorem h110 : Ban 120 5 v110 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w112 : ℕ := 0x800800800800800000000800800000000000000000000000000000000

def v111 : List ℕ := [w81,w82,w83,w112,w84,w85]

theorem h111 : Ban 120 5 v111 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w113 : ℕ := 0x880880880880880000000880880000000000000d9fd9f000000000000

def v112 : List ℕ := [w81,w82,w83,w113,w84,w85]

theorem h112 : Ban 120 5 v112 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v113 : List ℕ := [w81,w82,w83,w113,w85]

theorem h113 : Ban 120 5 v113 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w114 : ℕ := 0x980980980980980000000980980000000000000000d9f000000000000

def v114 : List ℕ := [w81,w82,w83,w114,w84,w85]

theorem h114 : Ban 120 5 v114 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w115 : ℕ := 0x980980980980980000000980980000000000000d9f000000000000000

def v115 : List ℕ := [w81,w82,w83,w115,w84,w85]

theorem h115 : Ban 120 5 v115 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w116 : ℕ := 0x98a98a98a98a98a00000098a98afff260260fffffffffffffff260fff

def v116 : List ℕ := [w81,w82,w83,w84,w116,w85]

theorem h116 : Ban 120 5 v116 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w117 : ℕ := 0x98c98c98c98c98c00000098c98c000000d9f000d9fd9f000000d9f000

def v117 : List ℕ := [w81,w82,w83,w84,w117,w85]

theorem h117 : Ban 120 5 v117 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w118 : ℕ := 0x990990990990990000000990990ffffff260260ffffffffffffffffff

def v118 : List ℕ := [w81,w82,w83,w84,w118,w85]

theorem h118 : Ban 120 5 v118 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w119 : ℕ := 0xc00c00c00c00c00000000c00c00000000d9fd9f000000000000000000

def v119 : List ℕ := [w81,w82,w83,w84,w119,w85]

theorem h119 : Ban 120 5 v119 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w120 : ℕ := 0xc00c00c00c00c00000000c00c00000d9f000d9f000000000000000000

def v120 : List ℕ := [w81,w82,w83,w84,w120,w85]

theorem h120 : Ban 120 5 v120 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w121 : ℕ := 0xc00c00c00c00c00000000c00c00000d9fd9f000000000000000000000

def v121 : List ℕ := [w81,w82,w83,w84,w121,w85]

theorem h121 : Ban 120 5 v121 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w122 : ℕ := 0xc0ac0ac0ac0ac0a000000c0ac0affffffffffff260fffffffff260fff

def v122 : List ℕ := [w81,w82,w83,w84,w85,w122]

theorem h122 : Ban 120 5 v122 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w123 : ℕ := 0xc10c10c10c10c10000000c10c10fffffffffffffff260ffffffffffff

def v123 : List ℕ := [w81,w82,w83,w84,w85,w123]

theorem h123 : Ban 120 5 v123 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w124 : ℕ := 0xd0cd0cd0cd0cd0c000000d0cd0c000d9fd9fd9f000000000000d9f000

def v124 : List ℕ := [w81,w82,w83,w84,w85,w124]

theorem h124 : Ban 120 5 v124 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w125 : ℕ := 0xd80d80d80d80d80000000d80d80000d9fd9fd9fd9fd9f000000000000

def v125 : List ℕ := [w81,w82,w83,w84,w85,w125]

theorem h125 : Ban 120 5 v125 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v126 : List ℕ := [w81,w82,w83,w84,w125]

theorem h126 : Ban 120 5 v126 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v127 : List ℕ := [w81,w82,w83,w117,w85]

theorem h127 : Ban 120 5 v127 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v128 : List ℕ := [w81,w82,w83,w85,w125]

theorem h128 : Ban 120 5 v128 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v129 : List ℕ := [w81,w82,w108,w84,w85]

theorem h129 : Ban 120 5 v129 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v130 : List ℕ := [w81,w82,w84,w117,w85]

theorem h130 : Ban 120 5 v130 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v131 : List ℕ := [w82,w83,w108,w84,w85]

theorem h131 : Ban 120 5 v131 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h79 : Ban 120 6 v79 := viaBranch (ws := [v80,v81,v82,v83,v84,v85,v86,v87,v88,v89,v90,v91,v92,v93,v94,v95,v96,v97,v98,v99,v100,v101,v102,v103,v104,v105,v106,v107,v108,v109,v110,v111,v112,v113,v114,v115,v116,v117,v118,v119,v120,v121,v122,v123,v124,v125,v126,v127,v128,v129,v130,v131])
  (consBan h80 (consBan h81 (consBan h82 (consBan h83 (consBan h84 (consBan h85 (consBan h86 (consBan h87 (consBan h88 (consBan h89 (consBan h90 (consBan h91 (consBan h92 (consBan h93 (consBan h94 (consBan h95 (consBan h96 (consBan h97 (consBan h98 (consBan h99 (consBan h100 (consBan h101 (consBan h102 (consBan h103 (consBan h104 (consBan h105 (consBan h106 (consBan h107 (consBan h108 (consBan h109 (consBan h110 (consBan h111 (consBan h112 (consBan h113 (consBan h114 (consBan h115 (consBan h116 (consBan h117 (consBan h118 (consBan h119 (consBan h120 (consBan h121 (consBan h122 (consBan h123 (consBan h124 (consBan h125 (consBan h126 (consBan h127 (consBan h128 (consBan h129 (consBan h130 (consBan h131 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def p107 : Projection 120 120 := pinchProj 120 0xd9fd9fd9fd9fd9f000000d9fd9f 0 (by decide) (by decide)

theorem minorant107 : Wide 120 6 v79 := widen (by decide +kernel) h79

theorem h78 : Ban 120 7 v78 := cutTest_ok p107 (extra := []) minorant107 (by decide) (by decide +kernel)

def w126 : ℕ := 0x40040040040040040040040040040000000000000000000000000000000

def v132 : List ℕ := [w0,w126,w1,w2,w3,w4,w5]

theorem h132 : Ban 120 7 v132 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w127 : ℕ := 0x50050050050050050050050050050000000000000fff000000000ffffff

def v133 : List ℕ := [w0,w127,w1,w2,w3,w4,w5]

theorem h133 : Ban 120 7 v133 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def w128 : ℕ := 0x50050050050050050050050050050000fff000000000000000000ffffff

def v134 : List ℕ := [w0,w128,w1,w2,w3,w4,w5]

theorem h134 : Ban 120 7 v134 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def w129 : ℕ := 0x50050050050050050050050050050000fff000000fff000000000000fff

def v135 : List ℕ := [w0,w129,w1,w2,w3,w4,w5]

theorem h135 : Ban 120 7 v135 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def w130 : ℕ := 0x50050050050050050050050050050000fff000000fff000000000fff000

def v136 : List ℕ := [w0,w130,w1,w2,w3,w4,w5]

theorem h136 : Ban 120 7 v136 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def w131 : ℕ := 0x5a05a05a05a05a05a05a05a05a05a000fff000fffffffff000fffffffff

def v137 : List ℕ := [w0,w1,w131,w2,w3,w4,w5]

def w132 : ℕ := 0x4000004000000000004000000000bdafffffffffffffffffffffffffff

def w133 : ℕ := 0x20000020000000000020000000000ffffffbdafffffffffffffffffffff

def w134 : ℕ := 0x400000400000000000400000000000425000425000000000000000000000

def v138 : List ℕ := [w132,w133,w134]

theorem h138 : Ban 120 3 v138 := viaSmall (by decide +kernel) (by decide)

def p82 : Projection 120 120 := pinchProj 120 0x425000425000000000425000000000 36 (by decide) (by decide)

theorem minorant82 : Wide 120 3 v138 := widen (by decide +kernel) h138

theorem h137 : Ban 120 7 v137 := cutTest_ok p82 (extra := []) minorant82 (by decide) (by decide +kernel)

def w135 : ℕ := 0x60060060060060060060060060060fff000000000000000ffffff000000

def v139 : List ℕ := [w0,w1,w135,w2,w3,w4,w5]

theorem h139 : Ban 120 7 v139 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v140 : List ℕ := [w0,w1,w135,w2,w4,w5]

theorem h140 : Ban 120 7 v140 := cutTest_ok p107 (extra := []) minorant107 (by decide) (by decide +kernel)

def w136 : ℕ := 0x100100100100100100100100100100000000000000000000000000000000

def v141 : List ℕ := [w0,w1,w136,w2,w3,w4,w5]

theorem h141 : Ban 120 7 v141 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w137 : ℕ := 0x104104104104104104104104104104000000fff000000000fff000fff000

def v142 : List ℕ := [w0,w1,w137,w2,w3,w4,w5]

theorem h142 : Ban 120 7 v142 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v143 : List ℕ := [w0,w1,w137,w3,w4,w5]

theorem h143 : Ban 120 7 v143 := cutTest_ok p121 (extra := []) minorant121 (by decide) (by decide +kernel)

def w138 : ℕ := 0x10c10c10c10c10c10c10c10c10c10c000000000000000000fff000fff000

def v144 : List ℕ := [w0,w1,w138,w2,w3,w4,w5]

theorem h144 : Ban 120 7 v144 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w139 : ℕ := 0x10c10c10c10c10c10c10c10c10c10c000000fff000000000000000fff000

def v145 : List ℕ := [w0,w1,w139,w2,w3,w4,w5]

theorem h145 : Ban 120 7 v145 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w140 : ℕ := 0x10c10c10c10c10c10c10c10c10c10c000000fff000000000fff000000000

def v146 : List ℕ := [w0,w1,w140,w2,w3,w4,w5]

theorem h146 : Ban 120 7 v146 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w141 : ℕ := 0x10e10e10e10e10e10e10e10e10e10e000000ffffff000fffffffffffffff

def v147 : List ℕ := [w0,w1,w2,w141,w3,w4,w5]

theorem h147 : Ban 120 7 v147 := cutTest_ok p121 (extra := []) minorant121 (by decide) (by decide +kernel)

def w142 : ℕ := 0x15c15c15c15c15c15c15c15c15c15c000ffffff000fff000fff000ffffff

def v148 : List ℕ := [w0,w1,w2,w142,w3,w4,w5]

theorem h148 : Ban 120 7 v148 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def w143 : ℕ := 0x200200200200200200200200200200000000000000000000000000000000

def v149 : List ℕ := [w0,w1,w2,w143,w3,w4,w5]

theorem h149 : Ban 120 7 v149 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w144 : ℕ := 0x220220220220220220220220220220fff000000000000000ffffff000000

def v150 : List ℕ := [w0,w1,w2,w144,w3,w4,w5]

theorem h150 : Ban 120 7 v150 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v151 : List ℕ := [w0,w1,w2,w144,w4,w5]

theorem h151 : Ban 120 7 v151 := cutTest_ok p107 (extra := []) minorant107 (by decide) (by decide +kernel)

def w145 : ℕ := 0x260260260260260260260260260260000000000000000000ffffff000000

def v152 : List ℕ := [w0,w1,w2,w145,w3,w4,w5]

theorem h152 : Ban 120 7 v152 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w146 : ℕ := 0x260260260260260260260260260260fff000000000000000000fff000000

def v153 : List ℕ := [w0,w1,w2,w146,w3,w4,w5]

theorem h153 : Ban 120 7 v153 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w147 : ℕ := 0x260260260260260260260260260260fff000000000000000fff000000000

def v154 : List ℕ := [w0,w1,w2,w147,w3,w4,w5]

theorem h154 : Ban 120 7 v154 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w148 : ℕ := 0x26a26a26a26a26a26a26a26a26a26afff000000fff000fffffffff000fff

def v155 : List ℕ := [w0,w1,w2,w3,w148,w4,w5]

theorem h155 : Ban 120 7 v155 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w149 : ℕ := 0x270270270270270270270270270270ffffff000000fff000ffffffffffff

def v156 : List ℕ := [w0,w1,w2,w3,w149,w4,w5]

theorem h156 : Ban 120 7 v156 := cutTest_ok p107 (extra := []) minorant107 (by decide) (by decide +kernel)

def w150 : ℕ := 0x36c36c36c36c36c36c36c36c36c36cfff000fff000000000fffffffff000

def v157 : List ℕ := [w0,w1,w2,w3,w150,w4,w5]

theorem h157 : Ban 120 7 v157 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w151 : ℕ := 0x380380380380380380380380380380000000000000ffffff000000000000

def v158 : List ℕ := [w0,w1,w2,w3,w151,w4,w5]

theorem h158 : Ban 120 7 v158 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v159 : List ℕ := [w0,w1,w2,w3,w151,w5]

def v160 : List ℕ := [w6,w0,w1,w2,w3,w151,w5]

theorem h160 : Ban 120 6 v160 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v161 : List ℕ := [w10,w0,w1,w2,w3,w151,w5]

theorem h161 : Ban 120 6 v161 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v162 : List ℕ := [w14,w0,w1,w2,w3,w151,w5]

theorem h162 : Ban 120 6 v162 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v163 : List ℕ := [w15,w0,w1,w2,w3,w151,w5]

theorem h163 : Ban 120 6 v163 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v164 : List ℕ := [w16,w0,w1,w2,w3,w151,w5]

theorem h164 : Ban 120 6 v164 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v165 : List ℕ := [w20,w0,w1,w2,w3,w151,w5]

theorem h165 : Ban 120 6 v165 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v166 : List ℕ := [w21,w0,w1,w2,w3,w151,w5]

theorem h166 : Ban 120 6 v166 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v167 : List ℕ := [w22,w0,w1,w2,w3,w151,w5]

theorem h167 : Ban 120 6 v167 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v168 : List ℕ := [w23,w0,w1,w2,w3,w151,w5]

theorem h168 : Ban 120 6 v168 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v169 : List ℕ := [w24,w0,w1,w2,w3,w151,w5]

theorem h169 : Ban 120 6 v169 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v170 : List ℕ := [w25,w0,w1,w2,w3,w151,w5]

theorem h170 : Ban 120 6 v170 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v171 : List ℕ := [w25,w1,w2,w3,w151,w5]

theorem h171 : Ban 120 6 v171 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v172 : List ℕ := [w74,w0,w1,w2,w3,w151,w5]

theorem h172 : Ban 120 6 v172 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v173 : List ℕ := [w75,w0,w1,w2,w3,w151,w5]

theorem h173 : Ban 120 6 v173 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v174 : List ℕ := [w76,w0,w1,w2,w3,w151,w5]

theorem h174 : Ban 120 6 v174 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v175 : List ℕ := [w77,w0,w1,w2,w3,w151,w5]

theorem h175 : Ban 120 6 v175 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v176 : List ℕ := [w78,w0,w1,w2,w3,w151,w5]

theorem h176 : Ban 120 6 v176 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v177 : List ℕ := [w0,w79,w1,w2,w3,w151,w5]

theorem h177 : Ban 120 6 v177 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v178 : List ℕ := [w0,w79,w1,w3,w151,w5]

theorem h178 : Ban 120 6 v178 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v179 : List ℕ := [w0,w80,w1,w2,w3,w151,w5]

theorem h179 : Ban 120 6 v179 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v180 : List ℕ := [w0,w80,w2,w3,w151,w5]

theorem h180 : Ban 120 6 v180 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v181 : List ℕ := [w0,w126,w1,w2,w3,w151,w5]

theorem h181 : Ban 120 6 v181 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v182 : List ℕ := [w0,w127,w1,w2,w3,w151,w5]

theorem h182 : Ban 120 6 v182 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v183 : List ℕ := [w0,w128,w1,w2,w3,w151,w5]

theorem h183 : Ban 120 6 v183 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v184 : List ℕ := [w0,w129,w1,w2,w3,w151,w5]

theorem h184 : Ban 120 6 v184 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v185 : List ℕ := [w0,w130,w1,w2,w3,w151,w5]

theorem h185 : Ban 120 6 v185 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v186 : List ℕ := [w0,w1,w131,w2,w3,w151,w5]

theorem h186 : Ban 120 6 v186 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v187 : List ℕ := [w0,w1,w135,w2,w3,w151,w5]

theorem h187 : Ban 120 6 v187 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v188 : List ℕ := [w0,w1,w135,w2,w151,w5]

theorem h188 : Ban 120 6 v188 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v189 : List ℕ := [w0,w1,w136,w2,w3,w151,w5]

theorem h189 : Ban 120 6 v189 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v190 : List ℕ := [w0,w1,w137,w2,w3,w151,w5]

theorem h190 : Ban 120 6 v190 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v191 : List ℕ := [w0,w1,w137,w3,w151,w5]

theorem h191 : Ban 120 6 v191 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v192 : List ℕ := [w0,w1,w138,w2,w3,w151,w5]

theorem h192 : Ban 120 6 v192 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v193 : List ℕ := [w0,w1,w139,w2,w3,w151,w5]

theorem h193 : Ban 120 6 v193 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v194 : List ℕ := [w0,w1,w140,w2,w3,w151,w5]

theorem h194 : Ban 120 6 v194 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v195 : List ℕ := [w0,w1,w2,w141,w3,w151,w5]

theorem h195 : Ban 120 6 v195 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v196 : List ℕ := [w0,w1,w2,w142,w3,w151,w5]

theorem h196 : Ban 120 6 v196 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w152 : ℕ := 0x180180180180180180180180180180000000000000ffffff000000000000

def v197 : List ℕ := [w0,w1,w2,w152,w3,w151,w5]

theorem h197 : Ban 120 6 v197 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v198 : List ℕ := [w0,w1,w2,w152,w3,w5]

theorem h198 : Ban 120 6 v198 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v199 : List ℕ := [w0,w1,w2,w143,w3,w151,w5]

theorem h199 : Ban 120 6 v199 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v200 : List ℕ := [w0,w1,w2,w144,w3,w151,w5]

theorem h200 : Ban 120 6 v200 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v201 : List ℕ := [w0,w1,w2,w144,w151,w5]

theorem h201 : Ban 120 6 v201 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v202 : List ℕ := [w0,w1,w2,w145,w3,w151,w5]

theorem h202 : Ban 120 6 v202 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v203 : List ℕ := [w0,w1,w2,w146,w3,w151,w5]

theorem h203 : Ban 120 6 v203 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v204 : List ℕ := [w0,w1,w2,w147,w3,w151,w5]

theorem h204 : Ban 120 6 v204 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v205 : List ℕ := [w0,w1,w2,w3,w148,w151,w5]

theorem h205 : Ban 120 6 v205 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v206 : List ℕ := [w0,w1,w2,w3,w149,w151,w5]

theorem h206 : Ban 120 6 v206 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w153 : ℕ := 0x280280280280280280280280280280000000000000ffffff000000000000

def v207 : List ℕ := [w0,w1,w2,w3,w153,w151,w5]

theorem h207 : Ban 120 6 v207 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v208 : List ℕ := [w0,w1,w2,w3,w153,w5]

theorem h208 : Ban 120 6 v208 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v209 : List ℕ := [w0,w1,w2,w3,w150,w151,w5]

theorem h209 : Ban 120 6 v209 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w154 : ℕ := 0x380380380380380380380380380380000000000000000fff000000000000

def v210 : List ℕ := [w0,w1,w2,w3,w154,w151,w5]

theorem h210 : Ban 120 6 v210 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w155 : ℕ := 0x380380380380380380380380380380000000000000fff000000000000000

def v211 : List ℕ := [w0,w1,w2,w3,w155,w151,w5]

theorem h211 : Ban 120 6 v211 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w156 : ℕ := 0x38a38a38a38a38a38a38a38a38a38a000000000fffffffff000fff000fff

def v212 : List ℕ := [w0,w1,w2,w3,w151,w156,w5]

theorem h212 : Ban 120 6 v212 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w157 : ℕ := 0x38c38c38c38c38c38c38c38c38c38c000000fff000fffffffff000fff000

def v213 : List ℕ := [w0,w1,w2,w3,w151,w157,w5]

theorem h213 : Ban 120 6 v213 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w158 : ℕ := 0x3d03d03d03d03d03d03d03d03d03d0000fff000000ffffff000000ffffff

def v214 : List ℕ := [w0,w1,w2,w3,w151,w158,w5]

theorem h214 : Ban 120 6 v214 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w159 : ℕ := 0x3e03e03e03e03e03e03e03e03e03e0fff000000000ffffffffffff000000

def v215 : List ℕ := [w0,w1,w2,w3,w151,w159,w5]

theorem h215 : Ban 120 6 v215 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w160 : ℕ := 0xc00c00c00c00c00c00c00c00c00c00000fffffffff000000000000000000

def v216 : List ℕ := [w0,w1,w2,w3,w151,w160,w5]

theorem h216 : Ban 120 6 v216 := viaSmall (by decide +kernel) (by decide)

def w161 : ℕ := 0xc00c00c00c00c00c00c00c00c00c00fff000ffffff000000000000000000

def v217 : List ℕ := [w0,w1,w2,w3,w151,w161,w5]

theorem h217 : Ban 120 6 v217 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w162 : ℕ := 0xc00c00c00c00c00c00c00c00c00c00ffffff000fff000000000000000000

def v218 : List ℕ := [w0,w1,w2,w3,w151,w162,w5]

theorem h218 : Ban 120 6 v218 := viaSmall (by decide +kernel) (by decide)

def w163 : ℕ := 0xc00c00c00c00c00c00c00c00c00c00fffffffff000000000000000000000

def v219 : List ℕ := [w0,w1,w2,w3,w151,w163,w5]

theorem h219 : Ban 120 6 v219 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w164 : ℕ := 0xc0ac0ac0ac0ac0ac0ac0ac0ac0ac0affffffffffff000fff000fff000fff

def v220 : List ℕ := [w0,w1,w2,w3,w151,w5,w164]

theorem h220 : Ban 120 6 v220 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w165 : ℕ := 0xc50c50c50c50c50c50c50c50c50c50fffffffffffffff000000000ffffff

def v221 : List ℕ := [w0,w1,w2,w3,w151,w5,w165]

theorem h221 : Ban 120 6 v221 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w166 : ℕ := 0xd0cd0cd0cd0cd0cd0cd0cd0cd0cd0cffffffffffff000000fff000fff000

def v222 : List ℕ := [w0,w1,w2,w3,w151,w5,w166]

theorem h222 : Ban 120 6 v222 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w167 : ℕ := 0xe60e60e60e60e60e60e60e60e60e60ffffffffffff000000ffffff000000

def v223 : List ℕ := [w0,w1,w2,w3,w151,w5,w167]

theorem h223 : Ban 120 6 v223 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w168 : ℕ := 0xf80f80f80f80f80f80f80f80f80f80ffffffffffffffffff000000000000

def v224 : List ℕ := [w0,w1,w2,w3,w151,w5,w168]

theorem h224 : Ban 120 6 v224 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v225 : List ℕ := [w0,w1,w2,w3,w151,w168]

theorem h225 : Ban 120 6 v225 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v226 : List ℕ := [w0,w1,w2,w3,w157,w5]

theorem h226 : Ban 120 6 v226 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v227 : List ℕ := [w0,w1,w2,w3,w159,w5]

theorem h227 : Ban 120 6 v227 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v228 : List ℕ := [w0,w1,w2,w3,w5,w168]

theorem h228 : Ban 120 6 v228 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v229 : List ℕ := [w0,w1,w2,w149,w151,w5]

theorem h229 : Ban 120 6 v229 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v230 : List ℕ := [w0,w1,w2,w151,w159,w5]

theorem h230 : Ban 120 6 v230 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v231 : List ℕ := [w0,w1,w141,w3,w151,w5]

theorem h231 : Ban 120 6 v231 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v232 : List ℕ := [w0,w1,w3,w151,w157,w5]

theorem h232 : Ban 120 6 v232 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v233 : List ℕ := [w0,w2,w3,w149,w151,w5]

theorem h233 : Ban 120 6 v233 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v234 : List ℕ := [w1,w2,w141,w3,w151,w5]

theorem h234 : Ban 120 6 v234 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h159 : Ban 120 7 v159 := viaBranch (ws := [v160,v161,v162,v163,v164,v165,v166,v167,v168,v169,v170,v171,v172,v173,v174,v175,v176,v177,v178,v179,v180,v181,v182,v183,v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232,v233,v234])
  (consBan h160 (consBan h161 (consBan h162 (consBan h163 (consBan h164 (consBan h165 (consBan h166 (consBan h167 (consBan h168 (consBan h169 (consBan h170 (consBan h171 (consBan h172 (consBan h173 (consBan h174 (consBan h175 (consBan h176 (consBan h177 (consBan h178 (consBan h179 (consBan h180 (consBan h181 (consBan h182 (consBan h183 (consBan h184 (consBan h185 (consBan h186 (consBan h187 (consBan h188 (consBan h189 (consBan h190 (consBan h191 (consBan h192 (consBan h193 (consBan h194 (consBan h195 (consBan h196 (consBan h197 (consBan h198 (consBan h199 (consBan h200 (consBan h201 (consBan h202 (consBan h203 (consBan h204 (consBan h205 (consBan h206 (consBan h207 (consBan h208 (consBan h209 (consBan h210 (consBan h211 (consBan h212 (consBan h213 (consBan h214 (consBan h215 (consBan h216 (consBan h217 (consBan h218 (consBan h219 (consBan h220 (consBan h221 (consBan h222 (consBan h223 (consBan h224 (consBan h225 (consBan h226 (consBan h227 (consBan h228 (consBan h229 (consBan h230 (consBan h231 (consBan h232 (consBan h233 (consBan h234 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def w169 : ℕ := 0x400400400400400400400400400400ffffffffffff000000000000000000

def v235 : List ℕ := [w0,w1,w2,w3,w169,w4]

def v236 : List ℕ := [w6,w0,w1,w2,w3,w169,w4]

theorem h236 : Ban 120 6 v236 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v237 : List ℕ := [w10,w0,w1,w2,w3,w169,w4]

theorem h237 : Ban 120 6 v237 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v238 : List ℕ := [w14,w0,w1,w2,w3,w169,w4]

theorem h238 : Ban 120 6 v238 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v239 : List ℕ := [w15,w0,w1,w2,w3,w169,w4]

theorem h239 : Ban 120 6 v239 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v240 : List ℕ := [w16,w0,w1,w2,w3,w169,w4]

theorem h240 : Ban 120 6 v240 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v241 : List ℕ := [w20,w0,w1,w2,w3,w169,w4]

theorem h241 : Ban 120 6 v241 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v242 : List ℕ := [w21,w0,w1,w2,w3,w169,w4]

theorem h242 : Ban 120 6 v242 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v243 : List ℕ := [w22,w0,w1,w2,w3,w169,w4]

theorem h243 : Ban 120 6 v243 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v244 : List ℕ := [w23,w0,w1,w2,w3,w169,w4]

theorem h244 : Ban 120 6 v244 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v245 : List ℕ := [w24,w0,w1,w2,w3,w169,w4]

theorem h245 : Ban 120 6 v245 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v246 : List ℕ := [w25,w0,w1,w2,w3,w169,w4]

theorem h246 : Ban 120 6 v246 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v247 : List ℕ := [w25,w1,w2,w3,w169,w4]

theorem h247 : Ban 120 6 v247 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v248 : List ℕ := [w74,w0,w1,w2,w3,w169,w4]

theorem h248 : Ban 120 6 v248 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v249 : List ℕ := [w75,w0,w1,w2,w3,w169,w4]

theorem h249 : Ban 120 6 v249 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v250 : List ℕ := [w76,w0,w1,w2,w3,w169,w4]

theorem h250 : Ban 120 6 v250 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v251 : List ℕ := [w77,w0,w1,w2,w3,w169,w4]

theorem h251 : Ban 120 6 v251 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v252 : List ℕ := [w78,w0,w1,w2,w3,w169,w4]

theorem h252 : Ban 120 6 v252 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v253 : List ℕ := [w0,w79,w1,w2,w3,w169,w4]

theorem h253 : Ban 120 6 v253 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v254 : List ℕ := [w0,w79,w1,w3,w169,w4]

theorem h254 : Ban 120 6 v254 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v255 : List ℕ := [w0,w80,w1,w2,w3,w169,w4]

theorem h255 : Ban 120 6 v255 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v256 : List ℕ := [w0,w80,w2,w3,w169,w4]

theorem h256 : Ban 120 6 v256 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v257 : List ℕ := [w0,w126,w1,w2,w3,w169,w4]

theorem h257 : Ban 120 6 v257 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v258 : List ℕ := [w0,w127,w1,w2,w3,w169,w4]

theorem h258 : Ban 120 6 v258 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v259 : List ℕ := [w0,w128,w1,w2,w3,w169,w4]

theorem h259 : Ban 120 6 v259 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v260 : List ℕ := [w0,w129,w1,w2,w3,w169,w4]

theorem h260 : Ban 120 6 v260 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v261 : List ℕ := [w0,w130,w1,w2,w3,w169,w4]

theorem h261 : Ban 120 6 v261 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v262 : List ℕ := [w0,w1,w131,w2,w3,w169,w4]

theorem h262 : Ban 120 6 v262 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v263 : List ℕ := [w0,w1,w135,w2,w3,w169,w4]

theorem h263 : Ban 120 6 v263 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v264 : List ℕ := [w0,w1,w135,w2,w169,w4]

theorem h264 : Ban 120 6 v264 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v265 : List ℕ := [w0,w1,w136,w2,w3,w169,w4]

theorem h265 : Ban 120 6 v265 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v266 : List ℕ := [w0,w1,w137,w2,w3,w169,w4]

theorem h266 : Ban 120 6 v266 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v267 : List ℕ := [w0,w1,w137,w3,w169,w4]

theorem h267 : Ban 120 6 v267 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v268 : List ℕ := [w0,w1,w138,w2,w3,w169,w4]

theorem h268 : Ban 120 6 v268 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v269 : List ℕ := [w0,w1,w139,w2,w3,w169,w4]

theorem h269 : Ban 120 6 v269 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v270 : List ℕ := [w0,w1,w140,w2,w3,w169,w4]

theorem h270 : Ban 120 6 v270 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v271 : List ℕ := [w0,w1,w2,w141,w3,w169,w4]

theorem h271 : Ban 120 6 v271 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v272 : List ℕ := [w0,w1,w2,w142,w3,w169,w4]

theorem h272 : Ban 120 6 v272 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v273 : List ℕ := [w0,w1,w2,w143,w3,w169,w4]

theorem h273 : Ban 120 6 v273 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v274 : List ℕ := [w0,w1,w2,w144,w3,w169,w4]

theorem h274 : Ban 120 6 v274 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v275 : List ℕ := [w0,w1,w2,w144,w169,w4]

theorem h275 : Ban 120 6 v275 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v276 : List ℕ := [w0,w1,w2,w145,w3,w169,w4]

theorem h276 : Ban 120 6 v276 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v277 : List ℕ := [w0,w1,w2,w146,w3,w169,w4]

theorem h277 : Ban 120 6 v277 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v278 : List ℕ := [w0,w1,w2,w147,w3,w169,w4]

theorem h278 : Ban 120 6 v278 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v279 : List ℕ := [w0,w1,w2,w3,w148,w169,w4]

theorem h279 : Ban 120 6 v279 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v280 : List ℕ := [w0,w1,w2,w3,w149,w169,w4]

theorem h280 : Ban 120 6 v280 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v281 : List ℕ := [w0,w1,w2,w3,w150,w169,w4]

theorem h281 : Ban 120 6 v281 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w170 : ℕ := 0x400400400400400400400400400400000fffffffff000000000000000000

def v282 : List ℕ := [w0,w1,w2,w3,w170,w169,w4]

theorem h282 : Ban 120 6 v282 := viaSmall (by decide +kernel) (by decide)

def w171 : ℕ := 0x400400400400400400400400400400fff000ffffff000000000000000000

def v283 : List ℕ := [w0,w1,w2,w3,w171,w169,w4]

theorem h283 : Ban 120 6 v283 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w172 : ℕ := 0x400400400400400400400400400400ffffff000fff000000000000000000

def v284 : List ℕ := [w0,w1,w2,w3,w172,w169,w4]

theorem h284 : Ban 120 6 v284 := viaSmall (by decide +kernel) (by decide)

def w173 : ℕ := 0x400400400400400400400400400400fffffffff000000000000000000000

def v285 : List ℕ := [w0,w1,w2,w3,w173,w169,w4]

theorem h285 : Ban 120 6 v285 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w174 : ℕ := 0x40a40a40a40a40a40a40a40a40a40affffffffffff000fff000fff000fff

def v286 : List ℕ := [w0,w1,w2,w3,w169,w174,w4]

theorem h286 : Ban 120 6 v286 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w175 : ℕ := 0x450450450450450450450450450450fffffffffffffff000000000ffffff

def v287 : List ℕ := [w0,w1,w2,w3,w169,w175,w4]

theorem h287 : Ban 120 6 v287 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w176 : ℕ := 0x50c50c50c50c50c50c50c50c50c50cffffffffffff000000fff000fff000

def v288 : List ℕ := [w0,w1,w2,w3,w169,w176,w4]

theorem h288 : Ban 120 6 v288 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w177 : ℕ := 0x660660660660660660660660660660ffffffffffff000000ffffff000000

def v289 : List ℕ := [w0,w1,w2,w3,w169,w177,w4]

theorem h289 : Ban 120 6 v289 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w178 : ℕ := 0x980980980980980980980980980980000000000000ffffff000000000000

def v290 : List ℕ := [w0,w1,w2,w3,w169,w178]

theorem h290 : Ban 120 6 v290 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v291 : List ℕ := [w0,w1,w2,w3,w169,w178,w4]

theorem h291 : Ban 120 6 v291 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w179 : ℕ := 0xa80a80a80a80a80a80a80a80a80a80000000000000ffffff000000000000

def v292 : List ℕ := [w0,w1,w2,w3,w169,w179]

theorem h292 : Ban 120 6 v292 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v293 : List ℕ := [w0,w1,w2,w3,w169,w179,w4]

theorem h293 : Ban 120 6 v293 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w180 : ℕ := 0xb80b80b80b80b80b80b80b80b80b80000000000000000fff000000000000

def v294 : List ℕ := [w0,w1,w2,w3,w169,w180,w4]

theorem h294 : Ban 120 6 v294 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w181 : ℕ := 0xb80b80b80b80b80b80b80b80b80b80000000000000fff000000000000000

def v295 : List ℕ := [w0,w1,w2,w3,w169,w181,w4]

theorem h295 : Ban 120 6 v295 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w182 : ℕ := 0xb8ab8ab8ab8ab8ab8ab8ab8ab8ab8a000000000fffffffff000fff000fff

def v296 : List ℕ := [w0,w1,w2,w3,w169,w4,w182]

theorem h296 : Ban 120 6 v296 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w183 : ℕ := 0xb8cb8cb8cb8cb8cb8cb8cb8cb8cb8c000000fff000fffffffff000fff000

def v297 : List ℕ := [w0,w1,w2,w3,w169,w4,w183]

theorem h297 : Ban 120 6 v297 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w184 : ℕ := 0xbd0bd0bd0bd0bd0bd0bd0bd0bd0bd0000fff000000ffffff000000ffffff

def v298 : List ℕ := [w0,w1,w2,w3,w169,w4,w184]

theorem h298 : Ban 120 6 v298 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w185 : ℕ := 0xbe0be0be0be0be0be0be0be0be0be0fff000000000ffffffffffff000000

def v299 : List ℕ := [w0,w1,w2,w3,w169,w4,w185]

theorem h299 : Ban 120 6 v299 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v300 : List ℕ := [w0,w1,w2,w3,w169,w4,w168]

theorem h300 : Ban 120 6 v300 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v301 : List ℕ := [w0,w1,w2,w3,w169,w183]

theorem h301 : Ban 120 6 v301 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v302 : List ℕ := [w0,w1,w2,w3,w169,w185]

theorem h302 : Ban 120 6 v302 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v303 : List ℕ := [w0,w1,w2,w3,w169,w168]

theorem h303 : Ban 120 6 v303 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v304 : List ℕ := [w0,w1,w2,w3,w4,w168]

theorem h304 : Ban 120 6 v304 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v305 : List ℕ := [w0,w1,w2,w149,w169,w4]

theorem h305 : Ban 120 6 v305 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v306 : List ℕ := [w0,w1,w2,w169,w4,w185]

theorem h306 : Ban 120 6 v306 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v307 : List ℕ := [w0,w1,w141,w3,w169,w4]

theorem h307 : Ban 120 6 v307 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v308 : List ℕ := [w0,w1,w3,w169,w4,w183]

theorem h308 : Ban 120 6 v308 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v309 : List ℕ := [w0,w2,w3,w149,w169,w4]

theorem h309 : Ban 120 6 v309 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v310 : List ℕ := [w1,w2,w141,w3,w169,w4]

theorem h310 : Ban 120 6 v310 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h235 : Ban 120 7 v235 := viaBranch (ws := [v236,v237,v238,v239,v240,v241,v242,v243,v244,v245,v246,v247,v248,v249,v250,v251,v252,v253,v254,v255,v256,v257,v258,v259,v260,v261,v262,v263,v264,v265,v266,v267,v268,v269,v270,v271,v272,v273,v274,v275,v276,v277,v278,v279,v280,v281,v282,v283,v284,v285,v286,v287,v288,v289,v290,v291,v292,v293,v294,v295,v296,v297,v298,v299,v300,v301,v302,v303,v304,v305,v306,v307,v308,v309,v310])
  (consBan h236 (consBan h237 (consBan h238 (consBan h239 (consBan h240 (consBan h241 (consBan h242 (consBan h243 (consBan h244 (consBan h245 (consBan h246 (consBan h247 (consBan h248 (consBan h249 (consBan h250 (consBan h251 (consBan h252 (consBan h253 (consBan h254 (consBan h255 (consBan h256 (consBan h257 (consBan h258 (consBan h259 (consBan h260 (consBan h261 (consBan h262 (consBan h263 (consBan h264 (consBan h265 (consBan h266 (consBan h267 (consBan h268 (consBan h269 (consBan h270 (consBan h271 (consBan h272 (consBan h273 (consBan h274 (consBan h275 (consBan h276 (consBan h277 (consBan h278 (consBan h279 (consBan h280 (consBan h281 (consBan h282 (consBan h283 (consBan h284 (consBan h285 (consBan h286 (consBan h287 (consBan h288 (consBan h289 (consBan h290 (consBan h291 (consBan h292 (consBan h293 (consBan h294 (consBan h295 (consBan h296 (consBan h297 (consBan h298 (consBan h299 (consBan h300 (consBan h301 (consBan h302 (consBan h303 (consBan h304 (consBan h305 (consBan h306 (consBan h307 (consBan h308 (consBan h309 (consBan h310 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v311 : List ℕ := [w0,w1,w2,w3,w169,w4,w5]

theorem h311 : Ban 120 7 v311 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w186 : ℕ := 0x800800800800800800800800800800000000000000000000000000000000

def v312 : List ℕ := [w0,w1,w2,w3,w186,w4,w5]

theorem h312 : Ban 120 7 v312 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v313 : List ℕ := [w0,w1,w2,w3,w178,w4,w5]

theorem h313 : Ban 120 7 v313 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v314 : List ℕ := [w0,w1,w2,w3,w178,w5]

theorem h314 : Ban 120 7 v314 := cutTest_ok p107 (extra := []) minorant107 (by decide) (by decide +kernel)

def v315 : List ℕ := [w0,w1,w2,w3,w179,w4,w5]

theorem h315 : Ban 120 7 v315 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v316 : List ℕ := [w0,w1,w2,w3,w179,w5]

theorem h316 : Ban 120 7 v316 := cutTest_ok p121 (extra := []) minorant121 (by decide) (by decide +kernel)

def v317 : List ℕ := [w0,w1,w2,w3,w180,w4,w5]

theorem h317 : Ban 120 7 v317 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v318 : List ℕ := [w0,w1,w2,w3,w181,w4,w5]

theorem h318 : Ban 120 7 v318 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v319 : List ℕ := [w0,w1,w2,w3,w4,w182,w5]

theorem h319 : Ban 120 7 v319 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v320 : List ℕ := [w0,w1,w2,w3,w4,w183,w5]

theorem h320 : Ban 120 7 v320 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v321 : List ℕ := [w0,w1,w2,w3,w4,w184,w5]

theorem h321 : Ban 120 7 v321 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v322 : List ℕ := [w0,w1,w2,w3,w4,w185,w5]

theorem h322 : Ban 120 7 v322 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v323 : List ℕ := [w0,w1,w2,w3,w4,w160,w5]

theorem h323 : Ban 120 7 v323 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v324 : List ℕ := [w0,w1,w2,w3,w4,w161,w5]

theorem h324 : Ban 120 7 v324 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v325 : List ℕ := [w0,w1,w2,w3,w4,w162,w5]

theorem h325 : Ban 120 7 v325 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v326 : List ℕ := [w0,w1,w2,w3,w4,w163,w5]

theorem h326 : Ban 120 7 v326 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v327 : List ℕ := [w0,w1,w2,w3,w4,w5,w164]

def w187 : ℕ := 0x5005005000005000005000005000000afff00afffffffff00afffffffff

def w188 : ℕ := 0x10410410400010400010400010400000a00affffff00afffffffffffffff

def w189 : ℕ := 0x260260260000260000260000260000ff5000000000000000ff5000000000

def w190 : ℕ := 0xb80b80b80000b80000b80000b80000000000000000ff5000000000000000

def w191 : ℕ := 0xc00c00c00000c00000c00000c00000ff5ff5ff5000000000000000000000

def v328 : List ℕ := [w187,w188,w189,w190,w191]

def w192 : ℕ := 0xff5000000000

def v329 : List ℕ := [w192,w187,w188,w189,w190,w191]

theorem h329 : Ban 120 5 v329 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w193 : ℕ := 0xff5000000000000000

def v330 : List ℕ := [w193,w187,w188,w189,w190,w191]

theorem h330 : Ban 120 5 v330 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v331 : List ℕ := [w193,w187,w188,w189,w191]

theorem h331 : Ban 120 5 v331 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w194 : ℕ := 0xff5000000000000000000000

def v332 : List ℕ := [w194,w187,w188,w189,w190,w191]

def w195 : ℕ := 0x50000050000050000ffffffffffffffffffc0afffffffff

def w196 : ℕ := 0x104000104000104000ffffffffffffc0afffffffffffffff

def w197 : ℕ := 0x2600002600002600000000000000000000003f5000000000

def w198 : ℕ := 0x3800003800003800000000000000003f5000000000000000

def v333 : List ℕ := [w195,w196,w197,w198]

theorem h333 : Ban 120 3 v333 := viaSmall (by decide +kernel) (by decide)

def p58 : Projection 120 120 := pinchProj 120 0x3f50003f50003f5000 12 (by decide) (by decide)

theorem minorant58 : Wide 120 3 v333 := widen (by decide +kernel) h333

theorem h332 : Ban 120 5 v332 := cutTest_ok p58 (extra := []) minorant58 (by decide) (by decide +kernel)

def w199 : ℕ := 0xff5000000000000000000000000

def v334 : List ℕ := [w199,w187,w188,w189,w190,w191]

theorem h334 : Ban 120 5 v334 := cutTest_ok p82 (extra := []) minorant82 (by decide) (by decide +kernel)

def w200 : ℕ := 0xa00a00afff00afff00afffffffff

def v335 : List ℕ := [w200,w187,w188,w189,w190,w191]

theorem h335 : Ban 120 5 v335 := cutTest_ok p82 (extra := []) minorant82 (by decide) (by decide +kernel)

def w201 : ℕ := 0xff5000000000000000000000000000

def v336 : List ℕ := [w201,w187,w188,w189,w190,w191]

theorem h336 : Ban 120 5 v336 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w202 : ℕ := 0x400400400000400000400000400000a00affffff00afffffffffffffff

def v337 : List ℕ := [w202,w187,w188,w189,w190,w191]

theorem h337 : Ban 120 5 v337 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v338 : List ℕ := [w202,w187,w189,w190,w191]

theorem h338 : Ban 120 5 v338 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w203 : ℕ := 0x1001001000001000001000001000000afff00afffffffff00afffffffff

def v339 : List ℕ := [w203,w187,w188,w189,w190,w191]

theorem h339 : Ban 120 5 v339 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v340 : List ℕ := [w203,w188,w189,w190,w191]

theorem h340 : Ban 120 5 v340 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w204 : ℕ := 0x40040040000040000040000040000000000000000000000000000000000

def v341 : List ℕ := [w204,w187,w188,w189,w190,w191]

theorem h341 : Ban 120 5 v341 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w205 : ℕ := 0x50050050000050000050000050000000ff5000000ff5000000000000000

def v342 : List ℕ := [w205,w187,w188,w189,w190,w191]

theorem h342 : Ban 120 5 v342 := cutTest_ok p82 (extra := []) minorant82 (by decide) (by decide +kernel)

def w206 : ℕ := 0x5005005000005000005000005000000a00a00afffffffff00afffffffff

def v343 : List ℕ := [w206,w187,w188,w189,w190,w191]

theorem h343 : Ban 120 5 v343 := cutTest_ok p82 (extra := []) minorant82 (by decide) (by decide +kernel)

def w207 : ℕ := 0x5005005000005000005000005000000afff00afff00afff00afffffffff

def v344 : List ℕ := [w207,w187,w188,w189,w190,w191]

theorem h344 : Ban 120 5 v344 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v345 : List ℕ := [w207,w187,w188,w189,w191]

theorem h345 : Ban 120 5 v345 := cutTest_ok p82 (extra := []) minorant82 (by decide) (by decide +kernel)

def w208 : ℕ := 0x60060060000060000060000060000ff5000000000000000ff5000000000

def v346 : List ℕ := [w187,w208,w188,w189,w190,w191]

theorem h346 : Ban 120 5 v346 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v347 : List ℕ := [w187,w208,w188,w190,w191]

theorem h347 : Ban 120 5 v347 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w209 : ℕ := 0x100100100000100000100000100000000000000000000000000000000000

def v348 : List ℕ := [w187,w209,w188,w189,w190,w191]

theorem h348 : Ban 120 5 v348 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w210 : ℕ := 0x104104104000104000104000104000000000ff5000000000ff5000000000

def v349 : List ℕ := [w187,w210,w188,w189,w190,w191]

theorem h349 : Ban 120 5 v349 := cutTest_ok p82 (extra := []) minorant82 (by decide) (by decide +kernel)

def w211 : ℕ := 0x10410410400010400010400010400000a00a00afff00afffffffffffffff

def v350 : List ℕ := [w187,w211,w188,w189,w190,w191]

def w212 : ℕ := 0x5005000000005000000000000000010efffffffffffffffffffffffffff

def w213 : ℕ := 0x260260000000260000000000000000ef1000000000000000000000000000

def w214 : ℕ := 0xa80a80000000a8000000000000000010e10effffffffffffffffffffffff

def w215 : ℕ := 0xc00c00000000c00000000000000000ef1ef1000000000000000000000000

def v351 : List ℕ := [w212,w213,w214,w215]

theorem h351 : Ban 120 3 v351 := viaSmall (by decide +kernel) (by decide)

def p120 : Projection 120 120 := pinchProj 120 0xef1ef1000000ef1000000000000000 60 (by decide) (by decide)

theorem minorant120 : Wide 120 3 v351 := widen (by decide +kernel) h351

theorem h350 : Ban 120 5 v350 := cutTest_ok p120 (extra := []) minorant120 (by decide) (by decide +kernel)

def w216 : ℕ := 0x10410410400010400010400010400000a00affffff00afff00afffffffff

def v352 : List ℕ := [w187,w216,w188,w189,w190,w191]

theorem h352 : Ban 120 5 v352 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w217 : ℕ := 0x15415415400015400015400015400000afffffffffffffffffffffffffff

def v353 : List ℕ := [w187,w188,w217,w189,w190,w191]

theorem h353 : Ban 120 5 v353 := cutTest_ok p82 (extra := []) minorant82 (by decide) (by decide +kernel)

def w218 : ℕ := 0x200200200000200000200000200000000000000000000000000000000000

def v354 : List ℕ := [w187,w188,w218,w189,w190,w191]

theorem h354 : Ban 120 5 v354 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w219 : ℕ := 0x220220220000220000220000220000ff5000000000000000ff5000000000

def v355 : List ℕ := [w187,w188,w219,w189,w190,w191]

theorem h355 : Ban 120 5 v355 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v356 : List ℕ := [w187,w188,w219,w190,w191]

theorem h356 : Ban 120 5 v356 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w220 : ℕ := 0x260260260000260000260000260000000000000000000000ff5000000000

def v357 : List ℕ := [w187,w188,w220,w189,w190,w191]

theorem h357 : Ban 120 5 v357 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w221 : ℕ := 0x260260260000260000260000260000ff5000000000000000000000000000

def v358 : List ℕ := [w187,w188,w221,w189,w190,w191]

theorem h358 : Ban 120 5 v358 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w222 : ℕ := 0x270270270000270000270000270000ffffff00afffffffffffffffffffff

def v359 : List ℕ := [w187,w188,w189,w222,w190,w191]

theorem h359 : Ban 120 5 v359 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w223 : ℕ := 0x364364364000364000364000364000fff00affffff00afffffffffffffff

def v360 : List ℕ := [w187,w188,w189,w223,w190,w191]

theorem h360 : Ban 120 5 v360 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w224 : ℕ := 0x380380380000380000380000380000000000000000ff5000000000000000

def v361 : List ℕ := [w187,w188,w189,w224,w190,w191]

theorem h361 : Ban 120 5 v361 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v362 : List ℕ := [w187,w188,w189,w224,w191]

theorem h362 : Ban 120 5 v362 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w225 : ℕ := 0x400400400000400000400000400000ff5ff5ff5000000000000000000000

def v363 : List ℕ := [w187,w188,w189,w225,w190]

theorem h363 : Ban 120 5 v363 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v364 : List ℕ := [w187,w188,w189,w225,w190,w191]

theorem h364 : Ban 120 5 v364 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w226 : ℕ := 0x800800800000800000800000800000000000000000000000000000000000

def v365 : List ℕ := [w187,w188,w189,w226,w190,w191]

theorem h365 : Ban 120 5 v365 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w227 : ℕ := 0x980980980000980000980000980000000000000000ff5000000000000000

def v366 : List ℕ := [w187,w188,w189,w227,w190,w191]

theorem h366 : Ban 120 5 v366 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v367 : List ℕ := [w187,w188,w189,w227,w191]

theorem h367 : Ban 120 5 v367 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w228 : ℕ := 0xa80a80a80000a80000a80000a80000000000000000ff5000000000000000

def v368 : List ℕ := [w187,w188,w189,w228,w190,w191]

theorem h368 : Ban 120 5 v368 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v369 : List ℕ := [w187,w188,w189,w228,w191]

theorem h369 : Ban 120 5 v369 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w229 : ℕ := 0xb80b80b80000b80000b80000b80000000000000000000000000000000000

def v370 : List ℕ := [w187,w188,w189,w229,w190,w191]

theorem h370 : Ban 120 5 v370 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w230 : ℕ := 0xb84b84b84000b84000b84000b8400000a00affffffffffffffffffffffff

def v371 : List ℕ := [w187,w188,w189,w190,w230,w191]

theorem h371 : Ban 120 5 v371 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w231 : ℕ := 0xbd0bd0bd0000bd0000bd0000bd000000afff00afffffffff00afffffffff

def v372 : List ℕ := [w187,w188,w189,w190,w231,w191]

theorem h372 : Ban 120 5 v372 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w232 : ℕ := 0xbe0be0be0000be0000be0000be0000ff5000000000ff5000ff5000000000

def v373 : List ℕ := [w187,w188,w189,w190,w232,w191]

theorem h373 : Ban 120 5 v373 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w233 : ℕ := 0xc00c00c00000c00000c00000c00000000ff5ff5000000000000000000000

def v374 : List ℕ := [w187,w188,w189,w190,w233,w191]

theorem h374 : Ban 120 5 v374 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w234 : ℕ := 0xc00c00c00000c00000c00000c00000ff5000ff5000000000000000000000

def v375 : List ℕ := [w187,w188,w189,w190,w234,w191]

theorem h375 : Ban 120 5 v375 := cutTest_ok p82 (extra := []) minorant82 (by decide) (by decide +kernel)

def w235 : ℕ := 0xc00c00c00000c00000c00000c00000ff5ff5000000000000000000000000

def v376 : List ℕ := [w187,w188,w189,w190,w235,w191]

theorem h376 : Ban 120 5 v376 := cutTest_ok p58 (extra := []) minorant58 (by decide) (by decide +kernel)

def w236 : ℕ := 0xc50c50c50000c50000c50000c50000ffffffffffffffffff00afffffffff

def v377 : List ℕ := [w187,w188,w189,w190,w191,w236]

theorem h377 : Ban 120 5 v377 := cutTest_ok p82 (extra := []) minorant82 (by decide) (by decide +kernel)

def w237 : ℕ := 0xd04d04d04000d04000d04000d04000ffffffffffff00afffffffffffffff

def v378 : List ℕ := [w187,w188,w189,w190,w191,w237]

theorem h378 : Ban 120 5 v378 := viaSmall (by decide +kernel) (by decide)

def w238 : ℕ := 0xe60e60e60000e60000e60000e60000ff5ff5ff5000000000ff5000000000

def v379 : List ℕ := [w187,w188,w189,w190,w191,w238]

theorem h379 : Ban 120 5 v379 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w239 : ℕ := 0xf80f80f80000f80000f80000f80000ff5ff5ff5000ff5000000000000000

def v380 : List ℕ := [w187,w188,w189,w190,w191,w239]

theorem h380 : Ban 120 5 v380 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v381 : List ℕ := [w187,w188,w189,w190,w239]

theorem h381 : Ban 120 5 v381 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v382 : List ℕ := [w187,w188,w189,w230,w191]

theorem h382 : Ban 120 5 v382 := viaSmall (by decide +kernel) (by decide)

def v383 : List ℕ := [w187,w188,w189,w232,w191]

theorem h383 : Ban 120 5 v383 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v384 : List ℕ := [w187,w188,w189,w191,w239]

theorem h384 : Ban 120 5 v384 := viaSmall (by decide +kernel) (by decide)

def v385 : List ℕ := [w187,w188,w222,w190,w191]

theorem h385 : Ban 120 5 v385 := cutTest_ok p82 (extra := []) minorant82 (by decide) (by decide +kernel)

def v386 : List ℕ := [w187,w188,w190,w232,w191]

theorem h386 : Ban 120 5 v386 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v387 : List ℕ := [w187,w189,w190,w230,w191]

theorem h387 : Ban 120 5 v387 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v388 : List ℕ := [w188,w189,w222,w190,w191]

theorem h388 : Ban 120 5 v388 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h328 : Ban 120 6 v328 := viaBranch (ws := [v329,v330,v331,v332,v334,v335,v336,v337,v338,v339,v340,v341,v342,v343,v344,v345,v346,v347,v348,v349,v350,v352,v353,v354,v355,v356,v357,v358,v359,v360,v361,v362,v363,v364,v365,v366,v367,v368,v369,v370,v371,v372,v373,v374,v375,v376,v377,v378,v379,v380,v381,v382,v383,v384,v385,v386,v387,v388])
  (consBan h329 (consBan h330 (consBan h331 (consBan h332 (consBan h334 (consBan h335 (consBan h336 (consBan h337 (consBan h338 (consBan h339 (consBan h340 (consBan h341 (consBan h342 (consBan h343 (consBan h344 (consBan h345 (consBan h346 (consBan h347 (consBan h348 (consBan h349 (consBan h350 (consBan h352 (consBan h353 (consBan h354 (consBan h355 (consBan h356 (consBan h357 (consBan h358 (consBan h359 (consBan h360 (consBan h361 (consBan h362 (consBan h363 (consBan h364 (consBan h365 (consBan h366 (consBan h367 (consBan h368 (consBan h369 (consBan h370 (consBan h371 (consBan h372 (consBan h373 (consBan h374 (consBan h375 (consBan h376 (consBan h377 (consBan h378 (consBan h379 (consBan h380 (consBan h381 (consBan h382 (consBan h383 (consBan h384 (consBan h385 (consBan h386 (consBan h387 (consBan h388 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def p122 : Projection 120 120 := pinchProj 120 0xff5ff5ff5000ff5000ff5000ff5000 12 (by decide) (by decide)

theorem minorant122 : Wide 120 6 v328 := widen (by decide +kernel) h328

theorem h327 : Ban 120 7 v327 := cutTest_ok p122 (extra := []) minorant122 (by decide) (by decide +kernel)

def v389 : List ℕ := [w0,w1,w2,w3,w4,w5,w165]

def w240 : ℕ := 0xa00000a00a00000a00a00a000000050fff050fffffffff050fffffffff

def w241 : ℕ := 0x10c00010c10c00010c10c10c000000000000faf000000000faf000000000

def w242 : ℕ := 0x220000220220000220220220000000ffffff050050fff050ffffffffffff

def w243 : ℕ := 0xb80000b80b80000b80b80b80000000000000000000000faf000000000000

def w244 : ℕ := 0xc00000c00c00000c00c00c00000000faf000faffaf000000000000000000

def v390 : List ℕ := [w240,w241,w242,w243,w244]

def w245 : ℕ := 0xfaf000000000

def v391 : List ℕ := [w245,w240,w241,w242,w243,w244]

theorem h391 : Ban 120 5 v391 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def w246 : ℕ := 0xfaf000000000000

def v392 : List ℕ := [w246,w240,w241,w242,w243,w244]

theorem h392 : Ban 120 5 v392 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v393 : List ℕ := [w246,w240,w241,w242,w244]

theorem h393 : Ban 120 5 v393 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def w247 : ℕ := 0xfaf000000000000000000

def v394 : List ℕ := [w247,w240,w241,w242,w243,w244]

theorem h394 : Ban 120 5 v394 := cutTest_ok p82 (extra := []) minorant82 (by decide) (by decide +kernel)

def w248 : ℕ := 0xfaf000000000000000000000

def v395 : List ℕ := [w248,w240,w241,w242,w243,w244]

theorem h395 : Ban 120 5 v395 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def w249 : ℕ := 0x50fff050050fff050050fffffffff

def v396 : List ℕ := [w249,w240,w241,w242,w243,w244]

theorem h396 : Ban 120 5 v396 := cutTest_ok p82 (extra := []) minorant82 (by decide) (by decide +kernel)

def w250 : ℕ := 0xfaf000000000000000000000000000

def v397 : List ℕ := [w250,w240,w241,w242,w243,w244]

def w251 : ℕ := 0xa00a00a000000ffffffffffffffffffc50fffffffff

def w252 : ℕ := 0x10c10c10c0000000000000000000000003af000000000

def w253 : ℕ := 0x220220220000000fffffffffffffffc50ffffffffffff

def w254 : ℕ := 0x3803803800000000000000000000003af000000000000

def v398 : List ℕ := [w251,w252,w253,w254]

theorem h398 : Ban 120 3 v398 := viaSmall (by decide +kernel) (by decide)

def p51 : Projection 120 120 := pinchProj 120 0x3af3af3af000000 24 (by decide) (by decide)

theorem minorant51 : Wide 120 3 v398 := widen (by decide +kernel) h398

theorem h397 : Ban 120 5 v397 := cutTest_ok p51 (extra := []) minorant51 (by decide) (by decide +kernel)

def w255 : ℕ := 0x2000002002000002002002000000050fff050fffffffff050fffffffff

def v399 : List ℕ := [w255,w240,w241,w242,w243,w244]

theorem h399 : Ban 120 5 v399 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v400 : List ℕ := [w255,w241,w242,w243,w244]

theorem h400 : Ban 120 5 v400 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def w256 : ℕ := 0x8000008008000008008008000000000000000000000000000000000000

def v401 : List ℕ := [w256,w240,w241,w242,w243,w244]

theorem h401 : Ban 120 5 v401 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def w257 : ℕ := 0xa00000a00a00000a00a00a000000000000000faf000faf000000000000

def v402 : List ℕ := [w257,w240,w241,w242,w243,w244]

theorem h402 : Ban 120 5 v402 := cutTest_ok p82 (extra := []) minorant82 (by decide) (by decide +kernel)

def w258 : ℕ := 0xa00000a00a00000a00a00a000000050fff050050ffffff050fffffffff

def v403 : List ℕ := [w258,w240,w241,w242,w243,w244]

theorem h403 : Ban 120 5 v403 := cutTest_ok p82 (extra := []) minorant82 (by decide) (by decide +kernel)

def w259 : ℕ := 0xa00000a00a00000a00a00a000000050fff050ffffff050050fffffffff

def v404 : List ℕ := [w259,w240,w241,w242,w243,w244]

theorem h404 : Ban 120 5 v404 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v405 : List ℕ := [w259,w240,w241,w242,w244]

theorem h405 : Ban 120 5 v405 := cutTest_ok p82 (extra := []) minorant82 (by decide) (by decide +kernel)

def w260 : ℕ := 0xc00000c00c00000c00c00c000000000000faf000000000faf000000000

def v406 : List ℕ := [w240,w260,w241,w242,w243,w244]

theorem h406 : Ban 120 5 v406 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v407 : List ℕ := [w240,w260,w242,w243,w244]

theorem h407 : Ban 120 5 v407 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def w261 : ℕ := 0x20000020020000020020020000000ffffff050050fff050ffffffffffff

def v408 : List ℕ := [w240,w261,w241,w242,w243,w244]

theorem h408 : Ban 120 5 v408 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v409 : List ℕ := [w240,w261,w241,w243,w244]

theorem h409 : Ban 120 5 v409 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def w262 : ℕ := 0x100000100100000100100100000000000000000000000000000000000000

def v410 : List ℕ := [w240,w262,w241,w242,w243,w244]

theorem h410 : Ban 120 5 v410 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def w263 : ℕ := 0x104000104104000104104104000000000000faf000000000faf000000000

def v411 : List ℕ := [w240,w263,w241,w242,w243,w244]

theorem h411 : Ban 120 5 v411 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v412 : List ℕ := [w240,w263,w242,w243,w244]

theorem h412 : Ban 120 5 v412 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def w264 : ℕ := 0x10c00010c10c00010c10c10c000000000000000000000000faf000000000

def v413 : List ℕ := [w240,w264,w241,w242,w243,w244]

theorem h413 : Ban 120 5 v413 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def w265 : ℕ := 0x10c00010c10c00010c10c10c000000000000faf000000000000000000000

def v414 : List ℕ := [w240,w265,w241,w242,w243,w244]

theorem h414 : Ban 120 5 v414 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def w266 : ℕ := 0x10e00010e10e00010e10e10e000000050fffffffffffffffffffffffffff

def v415 : List ℕ := [w240,w241,w266,w242,w243,w244]

theorem h415 : Ban 120 5 v415 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def w267 : ℕ := 0x200000200200000200200200000000000000000000000000000000000000

def v416 : List ℕ := [w240,w241,w267,w242,w243,w244]

theorem h416 : Ban 120 5 v416 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def w268 : ℕ := 0x220000220220000220220220000000050fff050050fff050ffffffffffff

def v417 : List ℕ := [w240,w241,w268,w242,w243,w244]

def w269 : ℕ := 0xa00a00000a000000000000ffffff270fffffffffffffffffffff

def w270 : ℕ := 0x10c10c00010c000000000000000000d8f000000000000000000000

def w271 : ℕ := 0x980980000980000000000000ffffff270270ffffffffffffffffff

def w272 : ℕ := 0xc00c00000c00000000000000000000d8fd8f000000000000000000

def v418 : List ℕ := [w269,w270,w271,w272]

theorem h418 : Ban 120 3 v418 := viaSmall (by decide +kernel) (by decide)

def p99 : Projection 120 120 := pinchProj 120 0xd8fd8f000d8f000000000000 48 (by decide) (by decide)

theorem minorant99 : Wide 120 3 v418 := widen (by decide +kernel) h418

theorem h417 : Ban 120 5 v417 := cutTest_ok p99 (extra := []) minorant99 (by decide) (by decide +kernel)

def w273 : ℕ := 0x220000220220000220220220000000faf000000000000000faf000000000

def v419 : List ℕ := [w240,w241,w273,w242,w243,w244]

theorem h419 : Ban 120 5 v419 := cutTest_ok p82 (extra := []) minorant82 (by decide) (by decide +kernel)

def w274 : ℕ := 0x220000220220000220220220000000ffffff050050fff050050fffffffff

def v420 : List ℕ := [w240,w241,w274,w242,w243,w244]

theorem h420 : Ban 120 5 v420 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def w275 : ℕ := 0x22a00022a22a00022a22a22a000000ffffff050fffffffffffffffffffff

def v421 : List ℕ := [w240,w241,w242,w275,w243,w244]

theorem h421 : Ban 120 5 v421 := cutTest_ok p82 (extra := []) minorant82 (by decide) (by decide +kernel)

def w276 : ℕ := 0x32c00032c32c00032c32c32c000000fffffffff050fff050ffffffffffff

def v422 : List ℕ := [w240,w241,w242,w276,w243,w244]

theorem h422 : Ban 120 5 v422 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def w277 : ℕ := 0x380000380380000380380380000000000000000000000faf000000000000

def v423 : List ℕ := [w240,w241,w242,w277,w243,w244]

theorem h423 : Ban 120 5 v423 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v424 : List ℕ := [w240,w241,w242,w277,w244]

theorem h424 : Ban 120 5 v424 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def w278 : ℕ := 0x400000400400000400400400000000faf000faffaf000000000000000000

def v425 : List ℕ := [w240,w241,w242,w278,w243]

theorem h425 : Ban 120 5 v425 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v426 : List ℕ := [w240,w241,w242,w278,w243,w244]

theorem h426 : Ban 120 5 v426 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def w279 : ℕ := 0x800000800800000800800800000000000000000000000000000000000000

def v427 : List ℕ := [w240,w241,w242,w279,w243,w244]

theorem h427 : Ban 120 5 v427 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def w280 : ℕ := 0x980000980980000980980980000000000000000000000faf000000000000

def v428 : List ℕ := [w240,w241,w242,w280,w243,w244]

theorem h428 : Ban 120 5 v428 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v429 : List ℕ := [w240,w241,w242,w280,w244]

theorem h429 : Ban 120 5 v429 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def w281 : ℕ := 0xa80000a80a80000a80a80a80000000000000000000000faf000000000000

def v430 : List ℕ := [w240,w241,w242,w281,w243,w244]

theorem h430 : Ban 120 5 v430 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v431 : List ℕ := [w240,w241,w242,w281,w244]

theorem h431 : Ban 120 5 v431 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def w282 : ℕ := 0xb80000b80b80000b80b80b80000000000000000000000000000000000000

def v432 : List ℕ := [w240,w241,w242,w282,w243,w244]

theorem h432 : Ban 120 5 v432 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def w283 : ℕ := 0xb8a000b8ab8a000b8ab8ab8a000000050fff050fffffffff050fffffffff

def v433 : List ℕ := [w240,w241,w242,w243,w283,w244]

theorem h433 : Ban 120 5 v433 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def w284 : ℕ := 0xb8c000b8cb8c000b8cb8cb8c000000000000faf000000faffaf000000000

def v434 : List ℕ := [w240,w241,w242,w243,w284,w244]

theorem h434 : Ban 120 5 v434 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def w285 : ℕ := 0xba0000ba0ba0000ba0ba0ba0000000ffffff050050ffffffffffffffffff

def v435 : List ℕ := [w240,w241,w242,w243,w285,w244]

theorem h435 : Ban 120 5 v435 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def w286 : ℕ := 0xc00000c00c00000c00c00c00000000000000faffaf000000000000000000

def v436 : List ℕ := [w240,w241,w242,w243,w286,w244]

theorem h436 : Ban 120 5 v436 := cutTest_ok p51 (extra := []) minorant51 (by decide) (by decide +kernel)

def w287 : ℕ := 0xc00000c00c00000c00c00c00000000faf000000faf000000000000000000

def v437 : List ℕ := [w240,w241,w242,w243,w287,w244]

theorem h437 : Ban 120 5 v437 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def w288 : ℕ := 0xc00000c00c00000c00c00c00000000faf000faf000000000000000000000

def v438 : List ℕ := [w240,w241,w242,w243,w288,w244]

theorem h438 : Ban 120 5 v438 := cutTest_ok p82 (extra := []) minorant82 (by decide) (by decide +kernel)

def w289 : ℕ := 0xc0a000c0ac0a000c0ac0ac0a000000ffffffffffffffffff050fffffffff

def v439 : List ℕ := [w240,w241,w242,w243,w244,w289]

theorem h439 : Ban 120 5 v439 := cutTest_ok p82 (extra := []) minorant82 (by decide) (by decide +kernel)

def w290 : ℕ := 0xd0c000d0cd0c000d0cd0cd0c000000faf000faffaf000000faf000000000

def v440 : List ℕ := [w240,w241,w242,w243,w244,w290]

theorem h440 : Ban 120 5 v440 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def w291 : ℕ := 0xe20000e20e20000e20e20e20000000fffffffffffffff050ffffffffffff

def v441 : List ℕ := [w240,w241,w242,w243,w244,w291]

theorem h441 : Ban 120 5 v441 := viaSmall (by decide +kernel) (by decide)

def w292 : ℕ := 0xf80000f80f80000f80f80f80000000faf000faffaf000faf000000000000

def v442 : List ℕ := [w240,w241,w242,w243,w244,w292]

theorem h442 : Ban 120 5 v442 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v443 : List ℕ := [w240,w241,w242,w243,w292]

theorem h443 : Ban 120 5 v443 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v444 : List ℕ := [w240,w241,w242,w284,w244]

theorem h444 : Ban 120 5 v444 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v445 : List ℕ := [w240,w241,w242,w285,w244]

theorem h445 : Ban 120 5 v445 := viaSmall (by decide +kernel) (by decide)

def v446 : List ℕ := [w240,w241,w242,w244,w292]

theorem h446 : Ban 120 5 v446 := viaSmall (by decide +kernel) (by decide)

def v447 : List ℕ := [w240,w241,w243,w285,w244]

theorem h447 : Ban 120 5 v447 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v448 : List ℕ := [w240,w266,w242,w243,w244]

theorem h448 : Ban 120 5 v448 := cutTest_ok p82 (extra := []) minorant82 (by decide) (by decide +kernel)

def v449 : List ℕ := [w240,w242,w243,w284,w244]

theorem h449 : Ban 120 5 v449 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v450 : List ℕ := [w241,w266,w242,w243,w244]

theorem h450 : Ban 120 5 v450 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h390 : Ban 120 6 v390 := viaBranch (ws := [v391,v392,v393,v394,v395,v396,v397,v399,v400,v401,v402,v403,v404,v405,v406,v407,v408,v409,v410,v411,v412,v413,v414,v415,v416,v417,v419,v420,v421,v422,v423,v424,v425,v426,v427,v428,v429,v430,v431,v432,v433,v434,v435,v436,v437,v438,v439,v440,v441,v442,v443,v444,v445,v446,v447,v448,v449,v450])
  (consBan h391 (consBan h392 (consBan h393 (consBan h394 (consBan h395 (consBan h396 (consBan h397 (consBan h399 (consBan h400 (consBan h401 (consBan h402 (consBan h403 (consBan h404 (consBan h405 (consBan h406 (consBan h407 (consBan h408 (consBan h409 (consBan h410 (consBan h411 (consBan h412 (consBan h413 (consBan h414 (consBan h415 (consBan h416 (consBan h417 (consBan h419 (consBan h420 (consBan h421 (consBan h422 (consBan h423 (consBan h424 (consBan h425 (consBan h426 (consBan h427 (consBan h428 (consBan h429 (consBan h430 (consBan h431 (consBan h432 (consBan h433 (consBan h434 (consBan h435 (consBan h436 (consBan h437 (consBan h438 (consBan h439 (consBan h440 (consBan h441 (consBan h442 (consBan h443 (consBan h444 (consBan h445 (consBan h446 (consBan h447 (consBan h448 (consBan h449 (consBan h450 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def p115 : Projection 120 120 := pinchProj 120 0xfaf000faffaf000faffaffaf000000 24 (by decide) (by decide)

theorem minorant115 : Wide 120 6 v390 := widen (by decide +kernel) h390

theorem h389 : Ban 120 7 v389 := cutTest_ok p115 (extra := []) minorant115 (by decide) (by decide +kernel)

def v451 : List ℕ := [w0,w1,w2,w3,w4,w5,w166]

theorem h451 : Ban 120 7 v451 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v452 : List ℕ := [w0,w1,w2,w3,w4,w5,w167]

theorem h452 : Ban 120 7 v452 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v453 : List ℕ := [w0,w1,w2,w3,w4,w5,w168]

def v454 : List ℕ := [w16,w0,w1,w2,w3,w5,w168]

theorem h454 : Ban 120 6 v454 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v455 : List ℕ := [w20,w0,w1,w2,w3,w5,w168]

theorem h455 : Ban 120 6 v455 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v456 : List ℕ := [w21,w0,w1,w2,w3,w4,w168]

theorem h456 : Ban 120 6 v456 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w293 : ℕ := 0xfff000fff000000000000

def v457 : List ℕ := [w293,w0,w1,w2,w3,w4,w5]

theorem h457 : Ban 120 6 v457 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v458 : List ℕ := [w22,w0,w1,w2,w3,w4,w168]

theorem h458 : Ban 120 6 v458 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v459 : List ℕ := [w23,w0,w1,w2,w3,w4,w168]

theorem h459 : Ban 120 6 v459 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w294 : ℕ := 0xfff000000fff000000000000000

def v460 : List ℕ := [w294,w0,w1,w2,w3,w4,w5]

theorem h460 : Ban 120 6 v460 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v461 : List ℕ := [w24,w0,w1,w2,w3,w4,w168]

theorem h461 : Ban 120 6 v461 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v462 : List ℕ := [w25,w1,w2,w3,w4,w5,w168]

theorem h462 : Ban 120 6 v462 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w295 : ℕ := 0xa00a00a00a00a00a00a00a00a00a000000000000000000000fff000fff

def v463 : List ℕ := [w295,w0,w1,w2,w3,w4,w5]

theorem h463 : Ban 120 6 v463 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v464 : List ℕ := [w75,w0,w1,w2,w3,w4,w168]

theorem h464 : Ban 120 6 v464 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v465 : List ℕ := [w76,w0,w1,w2,w3,w5,w168]

theorem h465 : Ban 120 6 v465 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w296 : ℕ := 0xc00c00c00c00c00c00c00c00c00c000000000000000000fff000fff000

def v466 : List ℕ := [w0,w296,w1,w2,w3,w4,w5]

theorem h466 : Ban 120 6 v466 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v467 : List ℕ := [w0,w79,w1,w2,w3,w5,w168]

theorem h467 : Ban 120 6 v467 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v468 : List ℕ := [w0,w79,w1,w3,w4,w5,w168]

theorem h468 : Ban 120 6 v468 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v469 : List ℕ := [w0,w79,w1,w3,w5,w168]

theorem h469 : Ban 120 6 v469 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v470 : List ℕ := [w0,w80,w2,w3,w4,w5,w168]

theorem h470 : Ban 120 6 v470 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w297 : ℕ := 0x50050050050050050050050050050000000000000000000000000ffffff

def v471 : List ℕ := [w0,w297,w1,w2,w3,w4,w5]

theorem h471 : Ban 120 6 v471 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v472 : List ℕ := [w0,w127,w1,w2,w3,w4,w168]

theorem h472 : Ban 120 6 v472 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v473 : List ℕ := [w0,w128,w1,w2,w3,w5,w168]

theorem h473 : Ban 120 6 v473 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def w298 : ℕ := 0x60060060060060060060060060060000000000000000000ffffff000000

def v474 : List ℕ := [w0,w1,w298,w2,w3,w4,w5]

theorem h474 : Ban 120 6 v474 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v475 : List ℕ := [w0,w1,w135,w2,w3,w5,w168]

theorem h475 : Ban 120 6 v475 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v476 : List ℕ := [w0,w1,w135,w2,w4,w5,w168]

theorem h476 : Ban 120 6 v476 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v477 : List ℕ := [w0,w1,w135,w2,w5,w168]

theorem h477 : Ban 120 6 v477 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v478 : List ℕ := [w0,w1,w136,w2,w3,w5,w168]

theorem h478 : Ban 120 6 v478 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w299 : ℕ := 0x100100100100100100100100100100000000fff000000000000000000000

def v479 : List ℕ := [w0,w1,w299,w2,w3,w4,w5]

theorem h479 : Ban 120 6 v479 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v480 : List ℕ := [w0,w1,w137,w3,w4,w5,w168]

theorem h480 : Ban 120 6 v480 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v481 : List ℕ := [w0,w1,w138,w2,w3,w4,w168]

theorem h481 : Ban 120 6 v481 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v482 : List ℕ := [w0,w1,w2,w143,w3,w5,w168]

theorem h482 : Ban 120 6 v482 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w300 : ℕ := 0x200200200200200200200200200200fff000000000000000000000000000

def v483 : List ℕ := [w0,w1,w2,w300,w3,w4,w5]

theorem h483 : Ban 120 6 v483 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v484 : List ℕ := [w0,w1,w2,w144,w4,w5,w168]

theorem h484 : Ban 120 6 v484 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v485 : List ℕ := [w0,w1,w2,w145,w3,w4,w168]

theorem h485 : Ban 120 6 v485 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

theorem h486 : Ban 120 6 v158 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v486 : List ℕ := [w0,w1,w2,w3,w151,w4,w168]

theorem h487 : Ban 120 6 v486 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

theorem h488 : Ban 120 6 v311 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v487 : List ℕ := [w0,w1,w2,w3,w169,w5,w168]

theorem h489 : Ban 120 6 v487 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v488 : List ℕ := [w0,w1,w2,w3,w186,w4,w168]

theorem h490 : Ban 120 6 v488 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v489 : List ℕ := [w0,w1,w2,w3,w186,w5,w168]

theorem h491 : Ban 120 6 v489 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v490 : List ℕ := [w0,w1,w2,w3,w178,w5,w168]

theorem h492 : Ban 120 6 v490 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v491 : List ℕ := [w0,w1,w2,w3,w179,w5,w168]

theorem h493 : Ban 120 6 v491 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v492 : List ℕ := [w0,w1,w2,w3,w180,w5,w168]

theorem h494 : Ban 120 6 v492 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v493 : List ℕ := [w0,w1,w2,w3,w181,w5,w168]

theorem h495 : Ban 120 6 v493 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v494 : List ℕ := [w0,w1,w2,w3,w4,w160,w168]

theorem h496 : Ban 120 6 v494 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v495 : List ℕ := [w0,w1,w2,w3,w4,w161,w168]

theorem h497 : Ban 120 6 v495 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v496 : List ℕ := [w0,w1,w2,w3,w4,w162,w168]

theorem h498 : Ban 120 6 v496 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v497 : List ℕ := [w0,w1,w2,w3,w4,w163,w168]

theorem h499 : Ban 120 6 v497 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w301 : ℕ := 0xd80d80d80d80d80d80d80d80d80d80000fffffffffffffff000000000000

def v498 : List ℕ := [w0,w1,w2,w3,w4,w5,w301]

theorem h500 : Ban 120 6 v498 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w302 : ℕ := 0xe80e80e80e80e80e80e80e80e80e80ffffff000fffffffff000000000000

def v499 : List ℕ := [w0,w1,w2,w3,w4,w5,w302]

theorem h501 : Ban 120 6 v499 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w303 : ℕ := 0xf80f80f80f80f80f80f80f80f80f80fff000ffffff000fff000000000000

def v500 : List ℕ := [w0,w1,w2,w3,w4,w5,w303]

theorem h502 : Ban 120 6 v500 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def w304 : ℕ := 0xf80f80f80f80f80f80f80f80f80f80fffffffff000fff000000000000000

def v501 : List ℕ := [w0,w1,w2,w3,w4,w5,w304]

theorem h503 : Ban 120 6 v501 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w305 : ℕ := 0xf8af8af8af8af8af8af8af8af8af8affffffffffffffffff000fff000fff

def v502 : List ℕ := [w0,w1,w2,w3,w4,w5,w305]

theorem h504 : Ban 120 6 v502 := viaSmall (by decide +kernel) (by decide)

def w306 : ℕ := 0xf8cf8cf8cf8cf8cf8cf8cf8cf8cf8cfffffffffffffffffffff000fff000

def v503 : List ℕ := [w0,w1,w2,w3,w4,w5,w306]

theorem h505 : Ban 120 6 v503 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w307 : ℕ := 0xfd0fd0fd0fd0fd0fd0fd0fd0fd0fd0ffffffffffffffffff000000ffffff

def v504 : List ℕ := [w0,w1,w2,w3,w4,w5,w307]

theorem h506 : Ban 120 6 v504 := viaSmall (by decide +kernel) (by decide)

def w308 : ℕ := 0xfe0fe0fe0fe0fe0fe0fe0fe0fe0fe0ffffffffffffffffffffffff000000

def v505 : List ℕ := [w0,w1,w2,w3,w4,w5,w308]

theorem h507 : Ban 120 6 v505 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v506 : List ℕ := [w0,w1,w2,w3,w4,w164,w168]

theorem h508 : Ban 120 6 v506 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v507 : List ℕ := [w0,w1,w2,w3,w4,w165,w168]

theorem h509 : Ban 120 6 v507 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v508 : List ℕ := [w0,w1,w2,w3,w4,w166,w168]

theorem h510 : Ban 120 6 v508 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v509 : List ℕ := [w0,w1,w2,w3,w4,w167,w168]

theorem h511 : Ban 120 6 v509 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v510 : List ℕ := [w0,w1,w2,w3,w182,w5,w168]

theorem h512 : Ban 120 6 v510 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v511 : List ℕ := [w0,w1,w2,w3,w183,w5,w168]

theorem h513 : Ban 120 6 v511 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v512 : List ℕ := [w0,w1,w2,w3,w184,w5,w168]

theorem h514 : Ban 120 6 v512 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v513 : List ℕ := [w0,w1,w2,w3,w185,w5,w168]

theorem h515 : Ban 120 6 v513 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v514 : List ℕ := [w0,w1,w2,w149,w4,w5,w168]

theorem h516 : Ban 120 6 v514 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v515 : List ℕ := [w0,w1,w2,w4,w185,w5,w168]

theorem h517 : Ban 120 6 v515 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v516 : List ℕ := [w0,w1,w141,w3,w4,w5,w168]

theorem h518 : Ban 120 6 v516 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v517 : List ℕ := [w0,w1,w3,w4,w183,w5,w168]

theorem h519 : Ban 120 6 v517 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v518 : List ℕ := [w0,w2,w3,w149,w4,w5,w168]

theorem h520 : Ban 120 6 v518 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v519 : List ℕ := [w1,w2,w141,w3,w4,w5,w168]

theorem h521 : Ban 120 6 v519 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h453 : Ban 120 7 v453 := viaBranch (ws := [v454,v455,v456,v457,v458,v459,v460,v461,v462,v463,v464,v465,v466,v467,v468,v469,v470,v471,v472,v473,v474,v475,v476,v477,v478,v479,v480,v481,v482,v483,v484,v485,v158,v486,v224,v225,v311,v300,v487,v303,v488,v489,v490,v491,v492,v493,v494,v495,v496,v497,v498,v499,v500,v501,v502,v503,v504,v505,v506,v507,v508,v509,v510,v511,v512,v513,v514,v515,v516,v517,v518,v519])
  (consBan h454 (consBan h455 (consBan h456 (consBan h457 (consBan h458 (consBan h459 (consBan h460 (consBan h461 (consBan h462 (consBan h463 (consBan h464 (consBan h465 (consBan h466 (consBan h467 (consBan h468 (consBan h469 (consBan h470 (consBan h471 (consBan h472 (consBan h473 (consBan h474 (consBan h475 (consBan h476 (consBan h477 (consBan h478 (consBan h479 (consBan h480 (consBan h481 (consBan h482 (consBan h483 (consBan h484 (consBan h485 (consBan h486 (consBan h487 (consBan h224 (consBan h225 (consBan h488 (consBan h300 (consBan h489 (consBan h303 (consBan h490 (consBan h491 (consBan h492 (consBan h493 (consBan h494 (consBan h495 (consBan h496 (consBan h497 (consBan h498 (consBan h499 (consBan h500 (consBan h501 (consBan h502 (consBan h503 (consBan h504 (consBan h505 (consBan h506 (consBan h507 (consBan h508 (consBan h509 (consBan h510 (consBan h511 (consBan h512 (consBan h513 (consBan h514 (consBan h515 (consBan h516 (consBan h517 (consBan h518 (consBan h519 (consBan h520 (consBan h521 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v520 : List ℕ := [w6,w0,w1,w2,w3,w4,w168]

theorem h523 : Ban 120 6 v520 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v521 : List ℕ := [w10,w0,w1,w2,w3,w4,w168]

theorem h524 : Ban 120 6 v521 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v522 : List ℕ := [w14,w0,w1,w2,w3,w4,w168]

theorem h525 : Ban 120 6 v522 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v523 : List ℕ := [w15,w0,w1,w2,w3,w4,w168]

theorem h526 : Ban 120 6 v523 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v524 : List ℕ := [w16,w0,w1,w2,w3,w4,w168]

theorem h527 : Ban 120 6 v524 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v525 : List ℕ := [w20,w0,w1,w2,w3,w4,w168]

theorem h528 : Ban 120 6 v525 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v526 : List ℕ := [w293,w0,w1,w2,w3,w4,w168]

theorem h529 : Ban 120 6 v526 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v527 : List ℕ := [w294,w0,w1,w2,w3,w4,w168]

theorem h530 : Ban 120 6 v527 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v528 : List ℕ := [w25,w0,w1,w2,w3,w4,w168]

theorem h531 : Ban 120 6 v528 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v529 : List ℕ := [w25,w1,w2,w3,w4,w168]

theorem h532 : Ban 120 6 v529 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v530 : List ℕ := [w74,w0,w1,w2,w3,w4,w168]

theorem h533 : Ban 120 6 v530 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v531 : List ℕ := [w295,w0,w1,w2,w3,w4,w168]

theorem h534 : Ban 120 6 v531 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v532 : List ℕ := [w76,w0,w1,w2,w3,w4,w168]

theorem h535 : Ban 120 6 v532 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v533 : List ℕ := [w77,w0,w1,w2,w3,w4,w168]

theorem h536 : Ban 120 6 v533 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v534 : List ℕ := [w78,w0,w1,w2,w3,w4,w168]

theorem h537 : Ban 120 6 v534 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v535 : List ℕ := [w0,w296,w1,w2,w3,w4,w168]

theorem h538 : Ban 120 6 v535 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v536 : List ℕ := [w0,w79,w1,w2,w3,w4,w168]

theorem h539 : Ban 120 6 v536 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v537 : List ℕ := [w0,w79,w1,w3,w4,w168]

theorem h540 : Ban 120 6 v537 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v538 : List ℕ := [w0,w80,w1,w2,w3,w4,w168]

theorem h541 : Ban 120 6 v538 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v539 : List ℕ := [w0,w80,w2,w3,w4,w168]

theorem h542 : Ban 120 6 v539 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v540 : List ℕ := [w0,w126,w1,w2,w3,w4,w168]

theorem h543 : Ban 120 6 v540 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v541 : List ℕ := [w0,w297,w1,w2,w3,w4,w168]

theorem h544 : Ban 120 6 v541 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v542 : List ℕ := [w0,w128,w1,w2,w3,w4,w168]

theorem h545 : Ban 120 6 v542 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v543 : List ℕ := [w0,w129,w1,w2,w3,w4,w168]

theorem h546 : Ban 120 6 v543 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v544 : List ℕ := [w0,w130,w1,w2,w3,w4,w168]

theorem h547 : Ban 120 6 v544 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v545 : List ℕ := [w0,w1,w131,w2,w3,w4,w168]

theorem h548 : Ban 120 6 v545 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v546 : List ℕ := [w0,w1,w298,w2,w3,w4,w168]

theorem h549 : Ban 120 6 v546 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v547 : List ℕ := [w0,w1,w135,w2,w3,w4,w168]

theorem h550 : Ban 120 6 v547 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v548 : List ℕ := [w0,w1,w135,w2,w4,w168]

theorem h551 : Ban 120 6 v548 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v549 : List ℕ := [w0,w1,w136,w2,w3,w4,w168]

theorem h552 : Ban 120 6 v549 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v550 : List ℕ := [w0,w1,w299,w2,w3,w4,w168]

theorem h553 : Ban 120 6 v550 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v551 : List ℕ := [w0,w1,w137,w2,w3,w4,w168]

theorem h554 : Ban 120 6 v551 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v552 : List ℕ := [w0,w1,w137,w3,w4,w168]

theorem h555 : Ban 120 6 v552 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v553 : List ℕ := [w0,w1,w139,w2,w3,w4,w168]

theorem h556 : Ban 120 6 v553 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v554 : List ℕ := [w0,w1,w140,w2,w3,w4,w168]

theorem h557 : Ban 120 6 v554 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v555 : List ℕ := [w0,w1,w2,w141,w3,w4,w168]

theorem h558 : Ban 120 6 v555 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v556 : List ℕ := [w0,w1,w2,w142,w3,w4,w168]

theorem h559 : Ban 120 6 v556 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v557 : List ℕ := [w0,w1,w2,w143,w3,w4,w168]

theorem h560 : Ban 120 6 v557 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v558 : List ℕ := [w0,w1,w2,w300,w3,w4,w168]

theorem h561 : Ban 120 6 v558 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v559 : List ℕ := [w0,w1,w2,w144,w3,w4,w168]

theorem h562 : Ban 120 6 v559 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v560 : List ℕ := [w0,w1,w2,w144,w4,w168]

theorem h563 : Ban 120 6 v560 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v561 : List ℕ := [w0,w1,w2,w146,w3,w4,w168]

theorem h564 : Ban 120 6 v561 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v562 : List ℕ := [w0,w1,w2,w147,w3,w4,w168]

theorem h565 : Ban 120 6 v562 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v563 : List ℕ := [w0,w1,w2,w3,w148,w4,w168]

theorem h566 : Ban 120 6 v563 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v564 : List ℕ := [w0,w1,w2,w3,w149,w4,w168]

theorem h567 : Ban 120 6 v564 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v565 : List ℕ := [w0,w1,w2,w3,w150,w4,w168]

theorem h568 : Ban 120 6 v565 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

theorem h569 : Ban 120 6 v235 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v566 : List ℕ := [w0,w1,w2,w3,w178,w4,w168]

theorem h570 : Ban 120 6 v566 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v567 : List ℕ := [w0,w1,w2,w3,w179,w4,w168]

theorem h571 : Ban 120 6 v567 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v568 : List ℕ := [w0,w1,w2,w3,w180,w4,w168]

theorem h572 : Ban 120 6 v568 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v569 : List ℕ := [w0,w1,w2,w3,w180,w168]

theorem h573 : Ban 120 6 v569 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v570 : List ℕ := [w0,w1,w2,w3,w181,w4,w168]

theorem h574 : Ban 120 6 v570 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v571 : List ℕ := [w0,w1,w2,w3,w181,w168]

theorem h575 : Ban 120 6 v571 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v572 : List ℕ := [w0,w1,w2,w3,w4,w182,w168]

theorem h576 : Ban 120 6 v572 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v573 : List ℕ := [w0,w1,w2,w3,w4,w183,w168]

theorem h577 : Ban 120 6 v573 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v574 : List ℕ := [w0,w1,w2,w3,w4,w184,w168]

theorem h578 : Ban 120 6 v574 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v575 : List ℕ := [w0,w1,w2,w3,w4,w185,w168]

theorem h579 : Ban 120 6 v575 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v576 : List ℕ := [w0,w1,w2,w3,w4,w301,w168]

theorem h580 : Ban 120 6 v576 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v577 : List ℕ := [w0,w1,w2,w3,w4,w302,w168]

theorem h581 : Ban 120 6 v577 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v578 : List ℕ := [w0,w1,w2,w3,w4,w303,w168]

theorem h582 : Ban 120 6 v578 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v579 : List ℕ := [w0,w1,w2,w3,w4,w304,w168]

theorem h583 : Ban 120 6 v579 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v580 : List ℕ := [w0,w1,w2,w3,w4,w168,w305]

theorem h584 : Ban 120 6 v580 := viaSmall (by decide +kernel) (by decide)

def v581 : List ℕ := [w0,w1,w2,w3,w4,w168,w306]

theorem h585 : Ban 120 6 v581 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v582 : List ℕ := [w0,w1,w2,w3,w4,w168,w307]

theorem h586 : Ban 120 6 v582 := viaSmall (by decide +kernel) (by decide)

def v583 : List ℕ := [w0,w1,w2,w3,w4,w168,w308]

theorem h587 : Ban 120 6 v583 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v584 : List ℕ := [w0,w1,w2,w3,w182,w168]

theorem h588 : Ban 120 6 v584 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v585 : List ℕ := [w0,w1,w2,w3,w184,w168]

theorem h589 : Ban 120 6 v585 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v586 : List ℕ := [w0,w1,w2,w149,w4,w168]

theorem h590 : Ban 120 6 v586 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v587 : List ℕ := [w0,w1,w2,w4,w185,w168]

theorem h591 : Ban 120 6 v587 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v588 : List ℕ := [w0,w1,w141,w3,w4,w168]

theorem h592 : Ban 120 6 v588 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v589 : List ℕ := [w0,w1,w3,w4,w183,w168]

theorem h593 : Ban 120 6 v589 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v590 : List ℕ := [w0,w2,w3,w149,w4,w168]

theorem h594 : Ban 120 6 v590 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v591 : List ℕ := [w1,w2,w141,w3,w4,w168]

theorem h595 : Ban 120 6 v591 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h522 : Ban 120 7 v304 := viaBranch (ws := [v520,v521,v522,v523,v524,v525,v526,v527,v528,v529,v530,v531,v532,v533,v534,v535,v536,v537,v538,v539,v540,v541,v542,v543,v544,v545,v546,v547,v548,v549,v550,v551,v552,v553,v554,v555,v556,v557,v558,v559,v560,v561,v562,v563,v564,v565,v235,v300,v303,v566,v567,v568,v569,v570,v571,v572,v573,v574,v575,v576,v577,v578,v579,v580,v581,v582,v583,v584,v585,v586,v587,v588,v589,v590,v591])
  (consBan h523 (consBan h524 (consBan h525 (consBan h526 (consBan h527 (consBan h528 (consBan h529 (consBan h530 (consBan h531 (consBan h532 (consBan h533 (consBan h534 (consBan h535 (consBan h536 (consBan h537 (consBan h538 (consBan h539 (consBan h540 (consBan h541 (consBan h542 (consBan h543 (consBan h544 (consBan h545 (consBan h546 (consBan h547 (consBan h548 (consBan h549 (consBan h550 (consBan h551 (consBan h552 (consBan h553 (consBan h554 (consBan h555 (consBan h556 (consBan h557 (consBan h558 (consBan h559 (consBan h560 (consBan h561 (consBan h562 (consBan h563 (consBan h564 (consBan h565 (consBan h566 (consBan h567 (consBan h568 (consBan h569 (consBan h300 (consBan h303 (consBan h570 (consBan h571 (consBan h572 (consBan h573 (consBan h574 (consBan h575 (consBan h576 (consBan h577 (consBan h578 (consBan h579 (consBan h580 (consBan h581 (consBan h582 (consBan h583 (consBan h584 (consBan h585 (consBan h586 (consBan h587 (consBan h588 (consBan h589 (consBan h590 (consBan h591 (consBan h592 (consBan h593 (consBan h594 (consBan h595 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v592 : List ℕ := [w0,w1,w2,w3,w183,w5]

theorem h596 : Ban 120 7 v592 := cutTest_ok p121 (extra := []) minorant121 (by decide) (by decide +kernel)

def v593 : List ℕ := [w0,w1,w2,w3,w185,w5]

theorem h597 : Ban 120 7 v593 := cutTest_ok p107 (extra := []) minorant107 (by decide) (by decide +kernel)

def v594 : List ℕ := [w6,w0,w1,w2,w3,w5,w168]

theorem h599 : Ban 120 6 v594 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v595 : List ℕ := [w10,w0,w1,w2,w3,w5,w168]

theorem h600 : Ban 120 6 v595 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v596 : List ℕ := [w14,w0,w1,w2,w3,w5,w168]

theorem h601 : Ban 120 6 v596 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v597 : List ℕ := [w15,w0,w1,w2,w3,w5,w168]

theorem h602 : Ban 120 6 v597 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v598 : List ℕ := [w21,w0,w1,w2,w3,w5,w168]

theorem h603 : Ban 120 6 v598 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v599 : List ℕ := [w293,w0,w1,w2,w3,w5,w168]

theorem h604 : Ban 120 6 v599 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v600 : List ℕ := [w22,w0,w1,w2,w3,w5,w168]

theorem h605 : Ban 120 6 v600 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v601 : List ℕ := [w23,w0,w1,w2,w3,w5,w168]

theorem h606 : Ban 120 6 v601 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v602 : List ℕ := [w294,w0,w1,w2,w3,w5,w168]

theorem h607 : Ban 120 6 v602 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v603 : List ℕ := [w24,w0,w1,w2,w3,w5,w168]

theorem h608 : Ban 120 6 v603 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v604 : List ℕ := [w25,w0,w1,w2,w3,w5,w168]

theorem h609 : Ban 120 6 v604 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v605 : List ℕ := [w25,w1,w2,w3,w5,w168]

theorem h610 : Ban 120 6 v605 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v606 : List ℕ := [w74,w0,w1,w2,w3,w5,w168]

theorem h611 : Ban 120 6 v606 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v607 : List ℕ := [w295,w0,w1,w2,w3,w5,w168]

theorem h612 : Ban 120 6 v607 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v608 : List ℕ := [w75,w0,w1,w2,w3,w5,w168]

theorem h613 : Ban 120 6 v608 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v609 : List ℕ := [w77,w0,w1,w2,w3,w5,w168]

theorem h614 : Ban 120 6 v609 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v610 : List ℕ := [w78,w0,w1,w2,w3,w5,w168]

theorem h615 : Ban 120 6 v610 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v611 : List ℕ := [w0,w296,w1,w2,w3,w5,w168]

theorem h616 : Ban 120 6 v611 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v612 : List ℕ := [w0,w80,w1,w2,w3,w5,w168]

theorem h617 : Ban 120 6 v612 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v613 : List ℕ := [w0,w80,w2,w3,w5,w168]

theorem h618 : Ban 120 6 v613 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v614 : List ℕ := [w0,w126,w1,w2,w3,w5,w168]

theorem h619 : Ban 120 6 v614 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v615 : List ℕ := [w0,w297,w1,w2,w3,w5,w168]

theorem h620 : Ban 120 6 v615 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v616 : List ℕ := [w0,w127,w1,w2,w3,w5,w168]

theorem h621 : Ban 120 6 v616 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v617 : List ℕ := [w0,w129,w1,w2,w3,w5,w168]

theorem h622 : Ban 120 6 v617 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v618 : List ℕ := [w0,w130,w1,w2,w3,w5,w168]

theorem h623 : Ban 120 6 v618 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v619 : List ℕ := [w0,w1,w131,w2,w3,w5,w168]

theorem h624 : Ban 120 6 v619 := cutTest_ok p82 (extra := []) minorant82 (by decide) (by decide +kernel)

def v620 : List ℕ := [w0,w1,w298,w2,w3,w5,w168]

theorem h625 : Ban 120 6 v620 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v621 : List ℕ := [w0,w1,w299,w2,w3,w5,w168]

theorem h626 : Ban 120 6 v621 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v622 : List ℕ := [w0,w1,w137,w2,w3,w5,w168]

theorem h627 : Ban 120 6 v622 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v623 : List ℕ := [w0,w1,w137,w3,w5,w168]

theorem h628 : Ban 120 6 v623 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v624 : List ℕ := [w0,w1,w138,w2,w3,w5,w168]

theorem h629 : Ban 120 6 v624 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v625 : List ℕ := [w0,w1,w139,w2,w3,w5,w168]

theorem h630 : Ban 120 6 v625 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v626 : List ℕ := [w0,w1,w140,w2,w3,w5,w168]

theorem h631 : Ban 120 6 v626 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v627 : List ℕ := [w0,w1,w2,w141,w3,w5,w168]

theorem h632 : Ban 120 6 v627 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v628 : List ℕ := [w0,w1,w2,w142,w3,w5,w168]

theorem h633 : Ban 120 6 v628 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v629 : List ℕ := [w0,w1,w2,w300,w3,w5,w168]

theorem h634 : Ban 120 6 v629 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v630 : List ℕ := [w0,w1,w2,w144,w3,w5,w168]

theorem h635 : Ban 120 6 v630 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v631 : List ℕ := [w0,w1,w2,w144,w5,w168]

theorem h636 : Ban 120 6 v631 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v632 : List ℕ := [w0,w1,w2,w145,w3,w5,w168]

theorem h637 : Ban 120 6 v632 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v633 : List ℕ := [w0,w1,w2,w146,w3,w5,w168]

theorem h638 : Ban 120 6 v633 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v634 : List ℕ := [w0,w1,w2,w147,w3,w5,w168]

theorem h639 : Ban 120 6 v634 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v635 : List ℕ := [w0,w1,w2,w3,w148,w5,w168]

theorem h640 : Ban 120 6 v635 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v636 : List ℕ := [w0,w1,w2,w3,w149,w5,w168]

theorem h641 : Ban 120 6 v636 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v637 : List ℕ := [w0,w1,w2,w3,w150,w5,w168]

theorem h642 : Ban 120 6 v637 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

theorem h643 : Ban 120 6 v159 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v638 : List ℕ := [w0,w1,w2,w3,w160,w5,w168]

theorem h644 : Ban 120 6 v638 := viaSmall (by decide +kernel) (by decide)

def v639 : List ℕ := [w0,w1,w2,w3,w161,w5,w168]

theorem h645 : Ban 120 6 v639 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v640 : List ℕ := [w0,w1,w2,w3,w161,w168]

theorem h646 : Ban 120 6 v640 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v641 : List ℕ := [w0,w1,w2,w3,w162,w5,w168]

theorem h647 : Ban 120 6 v641 := viaSmall (by decide +kernel) (by decide)

def v642 : List ℕ := [w0,w1,w2,w3,w163,w5,w168]

theorem h648 : Ban 120 6 v642 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v643 : List ℕ := [w0,w1,w2,w3,w163,w168]

theorem h649 : Ban 120 6 v643 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v644 : List ℕ := [w0,w1,w2,w3,w5,w164,w168]

theorem h650 : Ban 120 6 v644 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v645 : List ℕ := [w0,w1,w2,w3,w5,w165,w168]

theorem h651 : Ban 120 6 v645 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v646 : List ℕ := [w0,w1,w2,w3,w5,w166,w168]

theorem h652 : Ban 120 6 v646 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v647 : List ℕ := [w0,w1,w2,w3,w5,w301]

theorem h653 : Ban 120 6 v647 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v648 : List ℕ := [w0,w1,w2,w3,w5,w301,w168]

theorem h654 : Ban 120 6 v648 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v649 : List ℕ := [w0,w1,w2,w3,w5,w167,w168]

theorem h655 : Ban 120 6 v649 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v650 : List ℕ := [w0,w1,w2,w3,w5,w302]

theorem h656 : Ban 120 6 v650 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v651 : List ℕ := [w0,w1,w2,w3,w5,w302,w168]

theorem h657 : Ban 120 6 v651 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v652 : List ℕ := [w0,w1,w2,w3,w5,w303,w168]

theorem h658 : Ban 120 6 v652 := cutTest_ok p115 (extra := [w292]) minorant115 (by decide) (by decide +kernel)

def v653 : List ℕ := [w0,w1,w2,w3,w5,w304,w168]

theorem h659 : Ban 120 6 v653 := cutTest_ok p122 (extra := [w239]) minorant122 (by decide) (by decide +kernel)

def v654 : List ℕ := [w0,w1,w2,w3,w5,w168,w305]

theorem h660 : Ban 120 6 v654 := viaSmall (by decide +kernel) (by decide)

def v655 : List ℕ := [w0,w1,w2,w3,w5,w168,w306]

theorem h661 : Ban 120 6 v655 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v656 : List ℕ := [w0,w1,w2,w3,w5,w168,w307]

theorem h662 : Ban 120 6 v656 := viaSmall (by decide +kernel) (by decide)

def v657 : List ℕ := [w0,w1,w2,w3,w5,w168,w308]

theorem h663 : Ban 120 6 v657 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v658 : List ℕ := [w0,w1,w2,w3,w5,w306]

theorem h664 : Ban 120 6 v658 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v659 : List ℕ := [w0,w1,w2,w3,w5,w308]

theorem h665 : Ban 120 6 v659 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v660 : List ℕ := [w0,w1,w2,w3,w164,w168]

theorem h666 : Ban 120 6 v660 := cutTest_ok p122 (extra := [w239]) minorant122 (by decide) (by decide +kernel)

def v661 : List ℕ := [w0,w1,w2,w3,w165,w168]

theorem h667 : Ban 120 6 v661 := cutTest_ok p115 (extra := [w292]) minorant115 (by decide) (by decide +kernel)

def v662 : List ℕ := [w0,w1,w2,w149,w5,w168]

theorem h668 : Ban 120 6 v662 := cutTest_ok p115 (extra := [w292]) minorant115 (by decide) (by decide +kernel)

def v663 : List ℕ := [w0,w1,w141,w3,w5,w168]

theorem h669 : Ban 120 6 v663 := cutTest_ok p122 (extra := [w239]) minorant122 (by decide) (by decide +kernel)

def v664 : List ℕ := [w0,w2,w3,w149,w5,w168]

theorem h670 : Ban 120 6 v664 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v665 : List ℕ := [w1,w2,w141,w3,w5,w168]

theorem h671 : Ban 120 6 v665 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h598 : Ban 120 7 v228 := viaBranch (ws := [v594,v595,v596,v597,v598,v599,v600,v601,v602,v603,v604,v605,v606,v607,v608,v609,v610,v611,v612,v613,v614,v615,v616,v617,v618,v619,v620,v621,v622,v623,v624,v625,v626,v627,v628,v629,v630,v631,v632,v633,v634,v635,v636,v637,v159,v224,v225,v638,v639,v640,v641,v642,v643,v644,v645,v646,v647,v648,v649,v650,v651,v652,v653,v654,v655,v656,v657,v658,v659,v660,v661,v662,v663,v664,v665])
  (consBan h599 (consBan h600 (consBan h601 (consBan h602 (consBan h603 (consBan h604 (consBan h605 (consBan h606 (consBan h607 (consBan h608 (consBan h609 (consBan h610 (consBan h611 (consBan h612 (consBan h613 (consBan h614 (consBan h615 (consBan h616 (consBan h617 (consBan h618 (consBan h619 (consBan h620 (consBan h621 (consBan h622 (consBan h623 (consBan h624 (consBan h625 (consBan h626 (consBan h627 (consBan h628 (consBan h629 (consBan h630 (consBan h631 (consBan h632 (consBan h633 (consBan h634 (consBan h635 (consBan h636 (consBan h637 (consBan h638 (consBan h639 (consBan h640 (consBan h641 (consBan h642 (consBan h643 (consBan h224 (consBan h225 (consBan h644 (consBan h645 (consBan h646 (consBan h647 (consBan h648 (consBan h649 (consBan h650 (consBan h651 (consBan h652 (consBan h653 (consBan h654 (consBan h655 (consBan h656 (consBan h657 (consBan h658 (consBan h659 (consBan h660 (consBan h661 (consBan h662 (consBan h663 (consBan h664 (consBan h665 (consBan h666 (consBan h667 (consBan h668 (consBan h669 (consBan h670 (consBan h671 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v666 : List ℕ := [w0,w1,w2,w149,w4,w5]

theorem h672 : Ban 120 7 v666 := cutTest_ok p115 (extra := []) minorant115 (by decide) (by decide +kernel)

def v667 : List ℕ := [w0,w1,w2,w4,w185,w5]

def v668 : List ℕ := [w6,w0,w1,w2,w4,w185,w5]

theorem h674 : Ban 120 6 v668 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v669 : List ℕ := [w10,w0,w1,w2,w4,w185,w5]

theorem h675 : Ban 120 6 v669 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v670 : List ℕ := [w16,w0,w1,w2,w4,w185,w5]

theorem h676 : Ban 120 6 v670 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w309 : ℕ := 0xfff000fff000000

def v671 : List ℕ := [w309,w0,w1,w2,w4,w185,w5]

theorem h677 : Ban 120 6 v671 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v672 : List ℕ := [w20,w0,w1,w2,w4,w185,w5]

theorem h678 : Ban 120 6 v672 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v673 : List ℕ := [w21,w0,w1,w2,w4,w185,w5]

theorem h679 : Ban 120 6 v673 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v674 : List ℕ := [w22,w0,w1,w2,w4,w185,w5]

theorem h680 : Ban 120 6 v674 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v675 : List ℕ := [w23,w0,w1,w2,w4,w185,w5]

theorem h681 : Ban 120 6 v675 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v676 : List ℕ := [w25,w0,w1,w2,w4,w185,w5]

theorem h682 : Ban 120 6 v676 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v677 : List ℕ := [w25,w1,w2,w4,w185,w5]

theorem h683 : Ban 120 6 v677 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v678 : List ℕ := [w74,w0,w1,w2,w4,w185,w5]

theorem h684 : Ban 120 6 v678 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v679 : List ℕ := [w75,w0,w1,w2,w4,w185,w5]

theorem h685 : Ban 120 6 v679 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w310 : ℕ := 0xa00a00a00a00a00a00a00a00a00a000000000fff000000000000000fff

def v680 : List ℕ := [w310,w0,w1,w2,w4,w185,w5]

theorem h686 : Ban 120 6 v680 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v681 : List ℕ := [w76,w0,w1,w2,w4,w185,w5]

theorem h687 : Ban 120 6 v681 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v682 : List ℕ := [w78,w0,w1,w2,w4,w185,w5]

theorem h688 : Ban 120 6 v682 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w311 : ℕ := 0xc00c00c00c00c00c00c00c00c00c000000fff000000000000000fff000

def v683 : List ℕ := [w0,w311,w1,w2,w4,w185,w5]

theorem h689 : Ban 120 6 v683 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v684 : List ℕ := [w0,w79,w1,w2,w4,w185,w5]

theorem h690 : Ban 120 6 v684 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v685 : List ℕ := [w0,w79,w1,w4,w185,w5]

theorem h691 : Ban 120 6 v685 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w312 : ℕ := 0x10010010010010010010010010010000fff000000000000000000ffffff

def v686 : List ℕ := [w0,w312,w1,w2,w4,w185,w5]

theorem h692 : Ban 120 6 v686 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w313 : ℕ := 0x40040040040040040040040040040000000000000fff000000000000000

def v687 : List ℕ := [w0,w313,w1,w2,w4,w185,w5]

theorem h693 : Ban 120 6 v687 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v688 : List ℕ := [w0,w127,w1,w2,w4,w185,w5]

theorem h694 : Ban 120 6 v688 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v689 : List ℕ := [w0,w128,w1,w2,w4,w185,w5]

theorem h695 : Ban 120 6 v689 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v690 : List ℕ := [w0,w129,w1,w2,w4,w185,w5]

theorem h696 : Ban 120 6 v690 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v691 : List ℕ := [w0,w130,w1,w2,w4,w185,w5]

theorem h697 : Ban 120 6 v691 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v692 : List ℕ := [w0,w1,w131,w2,w4,w185,w5]

theorem h698 : Ban 120 6 v692 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v693 : List ℕ := [w0,w1,w135,w2,w4,w185,w5]

theorem h699 : Ban 120 6 v693 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

theorem h700 : Ban 120 6 v140 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v694 : List ℕ := [w0,w1,w135,w2,w185,w5]

theorem h701 : Ban 120 6 v694 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v695 : List ℕ := [w0,w1,w136,w2,w4,w185,w5]

theorem h702 : Ban 120 6 v695 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w314 : ℕ := 0x100100100100100100100100100100000000000000000000fff000000000

def v696 : List ℕ := [w0,w1,w314,w2,w4,w185,w5]

theorem h703 : Ban 120 6 v696 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v697 : List ℕ := [w0,w1,w137,w2,w4,w185,w5]

theorem h704 : Ban 120 6 v697 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v698 : List ℕ := [w0,w1,w137,w4,w185,w5]

theorem h705 : Ban 120 6 v698 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v699 : List ℕ := [w0,w1,w138,w2,w4,w185,w5]

theorem h706 : Ban 120 6 v699 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v700 : List ℕ := [w0,w1,w140,w2,w4,w185,w5]

theorem h707 : Ban 120 6 v700 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v701 : List ℕ := [w0,w1,w2,w141,w4,w185,w5]

theorem h708 : Ban 120 6 v701 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v702 : List ℕ := [w0,w1,w2,w142,w4,w185,w5]

theorem h709 : Ban 120 6 v702 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v703 : List ℕ := [w0,w1,w2,w151,w4,w185,w5]

theorem h710 : Ban 120 6 v703 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w315 : ℕ := 0x3e03e03e03e03e03e03e03e03e03e0000000000000ffffffffffff000000

def v704 : List ℕ := [w0,w1,w2,w315,w4,w185,w5]

theorem h711 : Ban 120 6 v704 := viaSmall (by decide +kernel) (by decide)

def v705 : List ℕ := [w0,w1,w2,w170,w4,w185,w5]

theorem h712 : Ban 120 6 v705 := viaSmall (by decide +kernel) (by decide)

def v706 : List ℕ := [w0,w1,w2,w169,w4,w185,w5]

theorem h713 : Ban 120 6 v706 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v707 : List ℕ := [w0,w1,w2,w186,w4,w185,w5]

theorem h714 : Ban 120 6 v707 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w316 : ℕ := 0x800800800800800800800800800800fff000000000000000000000000000

def v708 : List ℕ := [w0,w1,w2,w316,w4,w185,w5]

theorem h715 : Ban 120 6 v708 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v709 : List ℕ := [w0,w1,w2,w179,w4,w185,w5]

theorem h716 : Ban 120 6 v709 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w317 : ℕ := 0xae0ae0ae0ae0ae0ae0ae0ae0ae0ae0fff000000000ffffff000fff000000

def v710 : List ℕ := [w0,w1,w2,w317,w4,w185,w5]

theorem h717 : Ban 120 6 v710 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v711 : List ℕ := [w0,w1,w2,w180,w4,w185,w5]

theorem h718 : Ban 120 6 v711 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v712 : List ℕ := [w0,w1,w2,w181,w4,w185,w5]

theorem h719 : Ban 120 6 v712 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v713 : List ℕ := [w0,w1,w2,w181,w185,w5]

theorem h720 : Ban 120 6 v713 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v714 : List ℕ := [w0,w1,w2,w4,w182,w185,w5]

theorem h721 : Ban 120 6 v714 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v715 : List ℕ := [w0,w1,w2,w4,w183,w185,w5]

theorem h722 : Ban 120 6 v715 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w318 : ℕ := 0xba0ba0ba0ba0ba0ba0ba0ba0ba0ba0fff000000000000fffffffff000000

def v716 : List ℕ := [w0,w1,w2,w4,w318,w185,w5]

theorem h723 : Ban 120 6 v716 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v717 : List ℕ := [w0,w1,w2,w4,w318,w5]

theorem h724 : Ban 120 6 v717 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v718 : List ℕ := [w0,w1,w2,w4,w184,w185,w5]

theorem h725 : Ban 120 6 v718 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w319 : ℕ := 0xbe0be0be0be0be0be0be0be0be0be0fff000000000fff000fff000000000

def v719 : List ℕ := [w0,w1,w2,w4,w319,w185,w5]

theorem h726 : Ban 120 6 v719 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w320 : ℕ := 0xbeabeabeabeabeabeabeabeabeabeafff000000fffffffffffffff000fff

def v720 : List ℕ := [w0,w1,w2,w4,w185,w320,w5]

theorem h727 : Ban 120 6 v720 := viaSmall (by decide +kernel) (by decide)

def w321 : ℕ := 0xbecbecbecbecbecbecbecbecbecbecfff000fff000fffffffffffffff000

def v721 : List ℕ := [w0,w1,w2,w4,w185,w321,w5]

theorem h728 : Ban 120 6 v721 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w322 : ℕ := 0xbf0bf0bf0bf0bf0bf0bf0bf0bf0bf0ffffff000000ffffffffffffffffff

def v722 : List ℕ := [w0,w1,w2,w4,w185,w322,w5]

theorem h729 : Ban 120 6 v722 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v723 : List ℕ := [w0,w1,w2,w4,w185,w161,w5]

theorem h730 : Ban 120 6 v723 := viaSmall (by decide +kernel) (by decide)

def v724 : List ℕ := [w0,w1,w2,w4,w185,w162,w5]

theorem h731 : Ban 120 6 v724 := viaSmall (by decide +kernel) (by decide)

def v725 : List ℕ := [w0,w1,w2,w4,w185,w163,w5]

theorem h732 : Ban 120 6 v725 := viaSmall (by decide +kernel) (by decide)

def v726 : List ℕ := [w0,w1,w2,w4,w185,w5,w164]

theorem h733 : Ban 120 6 v726 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v727 : List ℕ := [w0,w1,w2,w4,w185,w5,w165]

theorem h734 : Ban 120 6 v727 := viaSmall (by decide +kernel) (by decide)

def v728 : List ℕ := [w0,w1,w2,w4,w185,w5,w166]

theorem h735 : Ban 120 6 v728 := viaSmall (by decide +kernel) (by decide)

def v729 : List ℕ := [w0,w1,w2,w4,w185,w5,w308]

theorem h736 : Ban 120 6 v729 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v730 : List ℕ := [w0,w1,w2,w4,w322,w5]

theorem h737 : Ban 120 6 v730 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v731 : List ℕ := [w0,w1,w2,w182,w185,w5]

theorem h738 : Ban 120 6 v731 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v732 : List ℕ := [w0,w1,w141,w4,w185,w5]

theorem h739 : Ban 120 6 v732 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v733 : List ℕ := [w0,w1,w4,w183,w185,w5]

theorem h740 : Ban 120 6 v733 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v734 : List ℕ := [w1,w2,w141,w4,w185,w5]

theorem h741 : Ban 120 6 v734 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h673 : Ban 120 7 v667 := viaBranch (ws := [v668,v669,v670,v671,v672,v673,v674,v675,v676,v677,v678,v679,v680,v681,v682,v683,v684,v685,v686,v687,v688,v689,v690,v691,v692,v693,v140,v694,v695,v696,v697,v698,v699,v700,v701,v702,v703,v704,v705,v306,v706,v707,v708,v709,v710,v711,v712,v713,v714,v715,v716,v717,v718,v719,v720,v721,v722,v723,v724,v725,v726,v727,v728,v515,v729,v587,v730,v731,v732,v733,v734])
  (consBan h674 (consBan h675 (consBan h676 (consBan h677 (consBan h678 (consBan h679 (consBan h680 (consBan h681 (consBan h682 (consBan h683 (consBan h684 (consBan h685 (consBan h686 (consBan h687 (consBan h688 (consBan h689 (consBan h690 (consBan h691 (consBan h692 (consBan h693 (consBan h694 (consBan h695 (consBan h696 (consBan h697 (consBan h698 (consBan h699 (consBan h700 (consBan h701 (consBan h702 (consBan h703 (consBan h704 (consBan h705 (consBan h706 (consBan h707 (consBan h708 (consBan h709 (consBan h710 (consBan h711 (consBan h712 (consBan h306 (consBan h713 (consBan h714 (consBan h715 (consBan h716 (consBan h717 (consBan h718 (consBan h719 (consBan h720 (consBan h721 (consBan h722 (consBan h723 (consBan h724 (consBan h725 (consBan h726 (consBan h727 (consBan h728 (consBan h729 (consBan h730 (consBan h731 (consBan h732 (consBan h733 (consBan h734 (consBan h735 (consBan h517 (consBan h736 (consBan h591 (consBan h737 (consBan h738 (consBan h739 (consBan h740 (consBan h741 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v735 : List ℕ := [w0,w1,w141,w3,w4,w5]

theorem h742 : Ban 120 7 v735 := cutTest_ok p122 (extra := []) minorant122 (by decide) (by decide +kernel)

def v736 : List ℕ := [w0,w1,w3,w4,w183,w5]

def v737 : List ℕ := [w6,w0,w1,w3,w4,w183,w5]

theorem h744 : Ban 120 6 v737 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v738 : List ℕ := [w14,w0,w1,w3,w4,w183,w5]

theorem h745 : Ban 120 6 v738 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v739 : List ℕ := [w16,w0,w1,w3,w4,w183,w5]

theorem h746 : Ban 120 6 v739 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v740 : List ℕ := [w20,w0,w1,w3,w4,w183,w5]

theorem h747 : Ban 120 6 v740 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w323 : ℕ := 0xfff000000000fff000

def v741 : List ℕ := [w323,w0,w1,w3,w4,w183,w5]

theorem h748 : Ban 120 6 v741 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v742 : List ℕ := [w21,w0,w1,w3,w4,w183,w5]

theorem h749 : Ban 120 6 v742 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v743 : List ℕ := [w23,w0,w1,w3,w4,w183,w5]

theorem h750 : Ban 120 6 v743 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v744 : List ℕ := [w24,w0,w1,w3,w4,w183,w5]

theorem h751 : Ban 120 6 v744 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w324 : ℕ := 0x2002002002002002002002002002000000000fff000000000fff000fff

def v745 : List ℕ := [w324,w0,w1,w3,w4,w183,w5]

theorem h752 : Ban 120 6 v745 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w325 : ℕ := 0x8008008008008008008008008008000000000000000fff000000000000

def v746 : List ℕ := [w325,w0,w1,w3,w4,w183,w5]

theorem h753 : Ban 120 6 v746 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v747 : List ℕ := [w75,w0,w1,w3,w4,w183,w5]

theorem h754 : Ban 120 6 v747 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v748 : List ℕ := [w76,w0,w1,w3,w4,w183,w5]

theorem h755 : Ban 120 6 v748 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v749 : List ℕ := [w77,w0,w1,w3,w4,w183,w5]

theorem h756 : Ban 120 6 v749 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v750 : List ℕ := [w78,w0,w1,w3,w4,w183,w5]

theorem h757 : Ban 120 6 v750 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v751 : List ℕ := [w0,w79,w1,w3,w4,w183,w5]

theorem h758 : Ban 120 6 v751 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

theorem h759 : Ban 120 6 v76 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v752 : List ℕ := [w0,w79,w1,w3,w183,w5]

theorem h760 : Ban 120 6 v752 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v753 : List ℕ := [w0,w80,w1,w3,w4,w183,w5]

theorem h761 : Ban 120 6 v753 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v754 : List ℕ := [w0,w80,w3,w4,w183,w5]

theorem h762 : Ban 120 6 v754 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v755 : List ℕ := [w0,w126,w1,w3,w4,w183,w5]

theorem h763 : Ban 120 6 v755 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v756 : List ℕ := [w0,w127,w1,w3,w4,w183,w5]

theorem h764 : Ban 120 6 v756 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def w326 : ℕ := 0x50050050050050050050050050050000fff000000000000000000000fff

def v757 : List ℕ := [w0,w326,w1,w3,w4,w183,w5]

theorem h765 : Ban 120 6 v757 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v758 : List ℕ := [w0,w128,w1,w3,w4,w183,w5]

theorem h766 : Ban 120 6 v758 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v759 : List ℕ := [w0,w130,w1,w3,w4,w183,w5]

theorem h767 : Ban 120 6 v759 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v760 : List ℕ := [w0,w1,w131,w3,w4,w183,w5]

theorem h768 : Ban 120 6 v760 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def w327 : ℕ := 0x60060060060060060060060060060fff000000000000000000fff000000

def v761 : List ℕ := [w0,w1,w327,w3,w4,w183,w5]

theorem h769 : Ban 120 6 v761 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v762 : List ℕ := [w0,w1,w135,w3,w4,w183,w5]

theorem h770 : Ban 120 6 v762 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v763 : List ℕ := [w0,w1,w135,w4,w183,w5]

theorem h771 : Ban 120 6 v763 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v764 : List ℕ := [w0,w1,w143,w3,w4,w183,w5]

theorem h772 : Ban 120 6 v764 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w328 : ℕ := 0x200200200200200200200200200200000000000000000000fff000000000

def v765 : List ℕ := [w0,w1,w328,w3,w4,w183,w5]

theorem h773 : Ban 120 6 v765 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v766 : List ℕ := [w0,w1,w144,w3,w4,w183,w5]

theorem h774 : Ban 120 6 v766 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v767 : List ℕ := [w0,w1,w144,w4,w183,w5]

theorem h775 : Ban 120 6 v767 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v768 : List ℕ := [w0,w1,w145,w3,w4,w183,w5]

theorem h776 : Ban 120 6 v768 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v769 : List ℕ := [w0,w1,w147,w3,w4,w183,w5]

theorem h777 : Ban 120 6 v769 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v770 : List ℕ := [w0,w1,w3,w148,w4,w183,w5]

theorem h778 : Ban 120 6 v770 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v771 : List ℕ := [w0,w1,w3,w149,w4,w183,w5]

theorem h779 : Ban 120 6 v771 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v772 : List ℕ := [w0,w1,w3,w151,w4,w183,w5]

theorem h780 : Ban 120 6 v772 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w329 : ℕ := 0x38c38c38c38c38c38c38c38c38c38c000000000000fffffffff000fff000

def v773 : List ℕ := [w0,w1,w3,w329,w4,w183,w5]

theorem h781 : Ban 120 6 v773 := viaSmall (by decide +kernel) (by decide)

def v774 : List ℕ := [w0,w1,w3,w172,w4,w183,w5]

theorem h782 : Ban 120 6 v774 := viaSmall (by decide +kernel) (by decide)

def v775 : List ℕ := [w0,w1,w3,w169,w4,w183,w5]

theorem h783 : Ban 120 6 v775 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v776 : List ℕ := [w0,w1,w3,w186,w4,w183,w5]

theorem h784 : Ban 120 6 v776 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def w330 : ℕ := 0x800800800800800800800800800800000000fff000000000000000000000

def v777 : List ℕ := [w0,w1,w3,w330,w4,w183,w5]

theorem h785 : Ban 120 6 v777 := cutTest_ok p41 (extra := []) minorant41 (by decide) (by decide +kernel)

def v778 : List ℕ := [w0,w1,w3,w178,w4,w183,w5]

theorem h786 : Ban 120 6 v778 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w331 : ℕ := 0x98c98c98c98c98c98c98c98c98c98c000000fff000ffffff000000fff000

def v779 : List ℕ := [w0,w1,w3,w331,w4,w183,w5]

theorem h787 : Ban 120 6 v779 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v780 : List ℕ := [w0,w1,w3,w180,w4,w183,w5]

theorem h788 : Ban 120 6 v780 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v781 : List ℕ := [w0,w1,w3,w180,w183,w5]

theorem h789 : Ban 120 6 v781 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v782 : List ℕ := [w0,w1,w3,w181,w4,w183,w5]

theorem h790 : Ban 120 6 v782 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w332 : ℕ := 0xb84b84b84b84b84b84b84b84b84b84000000fff000fff000fff000fff000

def v783 : List ℕ := [w0,w1,w3,w4,w332,w183,w5]

theorem h791 : Ban 120 6 v783 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v784 : List ℕ := [w0,w1,w3,w4,w332,w5]

theorem h792 : Ban 120 6 v784 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v785 : List ℕ := [w0,w1,w3,w4,w182,w183,w5]

theorem h793 : Ban 120 6 v785 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w333 : ℕ := 0xb8cb8cb8cb8cb8cb8cb8cb8cb8cb8c000000fff000000ffffff000000000

def v786 : List ℕ := [w0,w1,w3,w4,w333,w183,w5]

theorem h794 : Ban 120 6 v786 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w334 : ℕ := 0xb8eb8eb8eb8eb8eb8eb8eb8eb8eb8e000000ffffffffffffffffffffffff

def v787 : List ℕ := [w0,w1,w3,w4,w183,w334,w5]

theorem h795 : Ban 120 6 v787 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v788 : List ℕ := [w0,w1,w3,w4,w183,w184,w5]

theorem h796 : Ban 120 6 v788 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def w335 : ℕ := 0xbdcbdcbdcbdcbdcbdcbdcbdcbdcbdc000ffffff000fffffffff000ffffff

def v789 : List ℕ := [w0,w1,w3,w4,w183,w335,w5]

theorem h797 : Ban 120 6 v789 := viaSmall (by decide +kernel) (by decide)

def v790 : List ℕ := [w0,w1,w3,w4,w183,w185,w5]

theorem h798 : Ban 120 6 v790 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v791 : List ℕ := [w0,w1,w3,w4,w183,w321,w5]

theorem h799 : Ban 120 6 v791 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v792 : List ℕ := [w0,w1,w3,w4,w183,w160,w5]

theorem h800 : Ban 120 6 v792 := viaSmall (by decide +kernel) (by decide)

def v793 : List ℕ := [w0,w1,w3,w4,w183,w161,w5]

theorem h801 : Ban 120 6 v793 := viaSmall (by decide +kernel) (by decide)

def v794 : List ℕ := [w0,w1,w3,w4,w183,w163,w5]

theorem h802 : Ban 120 6 v794 := viaSmall (by decide +kernel) (by decide)

def v795 : List ℕ := [w0,w1,w3,w4,w183,w5,w164]

theorem h803 : Ban 120 6 v795 := viaSmall (by decide +kernel) (by decide)

def v796 : List ℕ := [w0,w1,w3,w4,w183,w5,w165]

theorem h804 : Ban 120 6 v796 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v797 : List ℕ := [w0,w1,w3,w4,w183,w5,w167]

theorem h805 : Ban 120 6 v797 := viaSmall (by decide +kernel) (by decide)

def v798 : List ℕ := [w0,w1,w3,w4,w183,w5,w306]

theorem h806 : Ban 120 6 v798 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

def v799 : List ℕ := [w0,w1,w3,w4,w334,w5]

theorem h807 : Ban 120 6 v799 := cutTest_ok p74 (extra := []) minorant74 (by decide) (by decide +kernel)

def v800 : List ℕ := [w0,w1,w3,w183,w184,w5]

theorem h808 : Ban 120 6 v800 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v801 : List ℕ := [w0,w1,w149,w4,w183,w5]

theorem h809 : Ban 120 6 v801 := cutTest_ok p81 (extra := []) minorant81 (by decide) (by decide +kernel)

def v802 : List ℕ := [w0,w3,w149,w4,w183,w5]

theorem h810 : Ban 120 6 v802 := cutTest_ok p73 (extra := []) minorant73 (by decide) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h743 : Ban 120 7 v736 := viaBranch (ws := [v737,v738,v739,v740,v741,v742,v743,v744,v745,v746,v747,v748,v749,v750,v751,v76,v752,v753,v754,v755,v756,v757,v758,v759,v760,v761,v762,v763,v764,v765,v766,v767,v768,v769,v770,v771,v772,v773,v774,v308,v775,v776,v777,v778,v779,v780,v781,v782,v783,v784,v785,v786,v787,v788,v789,v790,v791,v792,v793,v794,v795,v796,v797,v517,v798,v589,v799,v800,v801,v733,v802])
  (consBan h744 (consBan h745 (consBan h746 (consBan h747 (consBan h748 (consBan h749 (consBan h750 (consBan h751 (consBan h752 (consBan h753 (consBan h754 (consBan h755 (consBan h756 (consBan h757 (consBan h758 (consBan h759 (consBan h760 (consBan h761 (consBan h762 (consBan h763 (consBan h764 (consBan h765 (consBan h766 (consBan h767 (consBan h768 (consBan h769 (consBan h770 (consBan h771 (consBan h772 (consBan h773 (consBan h774 (consBan h775 (consBan h776 (consBan h777 (consBan h778 (consBan h779 (consBan h780 (consBan h781 (consBan h782 (consBan h308 (consBan h783 (consBan h784 (consBan h785 (consBan h786 (consBan h787 (consBan h788 (consBan h789 (consBan h790 (consBan h791 (consBan h792 (consBan h793 (consBan h794 (consBan h795 (consBan h796 (consBan h797 (consBan h798 (consBan h799 (consBan h800 (consBan h801 (consBan h802 (consBan h803 (consBan h804 (consBan h805 (consBan h519 (consBan h806 (consBan h593 (consBan h807 (consBan h808 (consBan h809 (consBan h740 (consBan h810 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

def v803 : List ℕ := [w0,w2,w3,w149,w4,w5]

theorem h811 : Ban 120 7 v803 := cutTest_ok p107 (extra := []) minorant107 (by decide) (by decide +kernel)

def v804 : List ℕ := [w1,w2,w141,w3,w4,w5]

theorem h812 : Ban 120 7 v804 := cutTest_ok p121 (extra := []) minorant121 (by decide) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem h0 : Ban 120 8 v0 := viaBranch (ws := [v1,v3,v5,v6,v7,v9,v10,v11,v12,v13,v14,v15,v70,v71,v72,v73,v74,v75,v76,v77,v78,v132,v133,v134,v135,v136,v137,v139,v140,v141,v142,v143,v144,v145,v146,v147,v148,v149,v150,v151,v152,v153,v154,v155,v156,v157,v158,v159,v235,v311,v312,v313,v314,v315,v316,v317,v318,v319,v320,v321,v322,v323,v324,v325,v326,v327,v389,v451,v452,v453,v304,v592,v593,v228,v666,v667,v735,v736,v803,v804])
  (consBan h1 (consBan h3 (consBan h5 (consBan h6 (consBan h7 (consBan h9 (consBan h10 (consBan h11 (consBan h12 (consBan h13 (consBan h14 (consBan h15 (consBan h70 (consBan h71 (consBan h72 (consBan h73 (consBan h74 (consBan h75 (consBan h76 (consBan h77 (consBan h78 (consBan h132 (consBan h133 (consBan h134 (consBan h135 (consBan h136 (consBan h137 (consBan h139 (consBan h140 (consBan h141 (consBan h142 (consBan h143 (consBan h144 (consBan h145 (consBan h146 (consBan h147 (consBan h148 (consBan h149 (consBan h150 (consBan h151 (consBan h152 (consBan h153 (consBan h154 (consBan h155 (consBan h156 (consBan h157 (consBan h158 (consBan h159 (consBan h235 (consBan h311 (consBan h312 (consBan h313 (consBan h314 (consBan h315 (consBan h316 (consBan h317 (consBan h318 (consBan h319 (consBan h320 (consBan h321 (consBan h322 (consBan h323 (consBan h324 (consBan h325 (consBan h326 (consBan h327 (consBan h389 (consBan h451 (consBan h452 (consBan h453 (consBan h522 (consBan h596 (consBan h597 (consBan h598 (consBan h672 (consBan h673 (consBan h742 (consBan h743 (consBan h811 (consBan h812 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)

theorem borneSix : Wide 120 8 sixBase := by
  apply widen (by decide +kernel)
  intro n hn hl
  exact h0 n hn (by simpa only [show sixBase.toFinset = v0.toFinset by decide +kernel] using hl)
end Travail11408


namespace Travail11408
open M10720 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def bouts : List ℕ := [0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6]

def graph (x : Fin 7 → Bool) := decide (∃ i < bouts.length / 2,
  (List.ofFn x).getD (bouts.getD (2*i) 0) false = true ∧
  (List.ofFn x).getD (bouts.getD (2*i+1) 0) false = true)

def temoin : List Gate := [
  ⟨.or,[0,1]⟩, ⟨.or,[3,4]⟩, ⟨.or,[0,3]⟩, ⟨.or,[9,2]⟩,
  ⟨.or,[7,8]⟩, ⟨.or,[11,2]⟩,
  ⟨.and,[7,8]⟩, ⟨.and,[10,5]⟩, ⟨.and,[12,6]⟩,
  ⟨.or,[13,14]⟩, ⟨.or,[16,15]⟩]

theorem legalite : ∀ g ∈ temoin, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [temoin]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
theorem correct : ∀ x : Fin 7 → Bool, Circuit.eval ⟨temoin,17⟩ (List.ofFn x) = graph x := by
  decide +kernel

def restriction : Projection 121 120 := pick (List.range 120) (by simp)
  (by intro i hi; have := List.mem_range.mp hi; omega) (by decide)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
theorem couper (h : Wide 120 8 sixBase) : Ban 121 9 septBase := by
  apply viaCut restriction h <;> decide +kernel

def sample (bank : ℕ) (i : Fin 121) (j : Fin 7) := bank.testBit (7*i.val+j.val)
def seeds : List Wire := septBase.map (fun a => (false,a))
set_option maxHeartbeats 1000000 in
theorem listed : ∀ i : Fin 121, seeds.map (read i.val)=List.ofFn (sample posBits i) ∧
    seeds.map (read (121+i.val))=List.ofFn (sample negBits i) := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem labels : ∀ i : Fin 121, graph (sample posBits i)=true ∧ graph (sample negBits i)=false := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem essential : ∀ a∈septBase, ∃ i : Fin 121, ∀ b∈septBase, b.testBit i.val≠b.testBit (121+i.val) → b=a := by decide +kernel
theorem initial {k S} (live : Live 121 k S) (sub : ∀ a∈S,a∈septBase) : S=septBase.toFinset := by
  apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
  intro a ha
  obtain ⟨i,h⟩ := essential a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
  exact h b (sub b hb) sep ▸ hb
theorem trace (C : Circuit) (fan : FanInTwo C) (eq : circuitFun 7 C=graph) :
    ∃ k≤C.gates.countP counted, Live 121 k septBase.toFinset := by
  let final := execute C.gates seeds
  let out := final.getD C.output zero
  have ev (i : ℕ) : read i out = C.eval (seeds.map (read i)) := by
    rw [show read i out = (final.map (read i)).getD C.output false from (read_get i final C.output).symm]
    rw [show final=execute C.gates seeds from rfl,execute_read i _ _ fan];rfl
  have result (x : Fin 7 → Bool) : C.eval (List.ofFn x)=graph x := congrFun eq x
  have good : Good 121 out.2 := by
    intro i hi same
    let j : Fin 121 := ⟨i,hi⟩
    have diff : M10720.read i out=M10720.read (121+i) out := by simp only [M10720.read,same]
    have p := ev i;have n := ev (121+i)
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


theorem finir (h : M10720.Wide 120 8 sixBase) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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


end Travail11408


end PEqualNP.Outside.L_meta_11407

theorem PEqualNP.Outside.L_meta_11407 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  exact PEqualNP.Outside.L_meta_11407.Travail11408.finir PEqualNP.Outside.L_meta_11407.Travail11408.borneSix
