import PEqualNP.Defs

-- The live-wire calculus is adapted from L-meta-10532. Fix input 1 to false.
-- The six remaining inputs require nine binary gates even with free negations.
-- Each search branch below either loses a separating pair or restricts to a smaller bank.
namespace PEqualNP.Outside.L_meta_11068.Example
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def f (x : Fin 7 → Bool) := decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
def witness : Circuit := ⟨[⟨.or,[0,1]⟩,⟨.or,[3,4]⟩,⟨.or,[7,8]⟩,⟨.or,[5,6]⟩,⟨.and,[9,10]⟩,
 ⟨.or,[7,2]⟩,⟨.or,[6,4]⟩,⟨.and,[12,13]⟩,⟨.and,[0,3]⟩,⟨.or,[11,14]⟩,⟨.or,[15,16]⟩],17⟩
theorem clean : Monotone2 witness := by simp [witness,Monotone2]
theorem size : witness.size = 11 := rfl
set_option maxRecDepth 10000 in
set_option maxHeartbeats 15000000 in
theorem computes : ∀ x, witness.eval (List.ofFn x) = f x := by decide +kernel
theorem sufficient (gs : List Gate) (h : 11 ≤ gs.length) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = f x :=
  ⟨witness.gates,witness.output,clean,h,computes⟩
end PEqualNP.Outside.L_meta_11068.Example


namespace PEqualNP.Outside.L_meta_11068

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

end PEqualNP.Outside.L_meta_11068

namespace PEqualNP.Outside.L_meta_11068

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

end PEqualNP.Outside.L_meta_11068

namespace PEqualNP.Outside.L_meta_11068
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







end PEqualNP.Outside.L_meta_11068

namespace PEqualNP.Outside.L_meta_11068
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

end PEqualNP.Outside.L_meta_11068

namespace PEqualNP.Outside.L_meta_11068
def f0 : ℕ := 0x11005115081300f33f
def f1 : ℕ := 0x10944cc54c309c4ccdcc
def f2 : ℕ := 0x4a0850e0a44e08f0e0f
def f3 : ℕ := 0x500900aa08700f00ff0
def f4 : ℕ := 0xf8006aa000f800fff000
def f5 : ℕ := 0xea4a000000ffff000000
def s0 : List ℕ := [f0,f1,f2,f3,f4,f5]
def f6 : ℕ := 0x10004104001000c10c
def s1 : List ℕ := [f6,f0,f2,f3,f1,f5,f4]
def rho0 : Projection 40 6 := pick [0,1,12,13,16,17] (by decide) (by decide) (by decide)
def f7 : ℕ := 0x14f
def f8 : ℕ := 0x4b3
def f9 : ℕ := 0xa3c
def s2 : List ℕ := [f7,f8,f9]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w0 : Wide 6 3 s2 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof1 : Ban 40 7 s1 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f10 : ℕ := 0x10954cd55d389f4cffff
def s3 : List ℕ := [f0,f2,f3,f10,f5,f4]
def f11 : ℕ := 0x20f
def s4 : List ℕ := [f11,f0,f2,f3,f10,f5,f4]
def rho1 : Projection 40 6 := pick [6,7,26,27,32,33] (by decide) (by decide) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w1 : Wide 6 2 s2 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof3 : Ban 40 6 s4 := viaCut rho1 w1 (by decide) (by decide +kernel) (by decide +kernel)
def f12 : ℕ := 0x4b1855f1f4cf38fff3f
def s5 : List ℕ := [f0,f2,f12,f3,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof4 : Ban 40 6 s5 := viaSmall (by decide +kernel) (by decide)
def f13 : ℕ := 0x4a0850e0a44e08f0c00
def s6 : List ℕ := [f0,f13,f2,f3,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof5 : Ban 40 6 s6 := viaSmall (by decide +kernel) (by decide)
def f14 : ℕ := 0x11005115081300f130
def s7 : List ℕ := [f14,f0,f2,f3,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof6 : Ban 40 6 s7 := viaSmall (by decide +kernel) (by decide)
def f15 : ℕ := 0x330
def s8 : List ℕ := [f15,f0,f2,f3,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof7 : Ban 40 6 s8 := viaCut rho1 w1 (by decide) (by decide +kernel) (by decide +kernel)
def f16 : ℕ := 0x511905bb58f13f0ffff
def s9 : List ℕ := [f2,f3,f16,f10,f5,f4]
def rho2 : Weak 40 8 := signedPick 0 [0,2,3,12,14,15,18,19] (by decide) (by decide) (by decide)
def f17 : ℕ := 0xa0f8
def f18 : ℕ := 0xbb38
def f19 : ℕ := 0xe4c0
def s10 : List ℕ := [f17,f18,f19]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w2 : Wide 8 3 s10 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof8 : Ban 40 6 s9 := viaWeakCut rho2 w2 (by decide) (by decide +kernel) (by decide +kernel)
def s11 : List ℕ := [f0,f2,f3,f16,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof9 : Ban 40 6 s11 := viaCut rho1 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f20 : ℕ := 0x500900aa08700f00cc0
def s12 : List ℕ := [f0,f2,f20,f3,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof10 : Ban 40 6 s12 := viaCut rho1 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f21 : ℕ := 0x11005115081300f00f
def s13 : List ℕ := [f21,f2,f3,f10,f5,f4]
def rho3 : Projection 40 7 := pick [5,6,7,26,27,32,33] (by decide) (by decide) (by decide)
def f22 : ℕ := 0x51f
def f23 : ℕ := 0x12e7
def f24 : ℕ := 0x2878
def s14 : List ℕ := [f22,f23,f24]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w3 : Wide 7 3 s14 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof11 : Ban 40 6 s13 := viaCut rho3 w3 (by decide) (by decide +kernel) (by decide +kernel)
def s15 : List ℕ := [f21,f0,f2,f3,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof12 : Ban 40 6 s15 := viaSmall (by decide +kernel) (by decide)
def f25 : ℕ := 0x400800a000400800e00
def s16 : List ℕ := [f0,f25,f2,f3,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof13 : Ban 40 6 s16 := viaSmall (by decide +kernel) (by decide)
def f26 : ℕ := 0x5a0950eaac7e0ff0fff
def s17 : List ℕ := [f0,f3,f26,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof14 : Ban 40 6 s17 := viaWeakCut rho2 w2 (by decide) (by decide +kernel) (by decide +kernel)
def s18 : List ℕ := [f0,f2,f3,f26,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof15 : Ban 40 6 s18 := viaSmall (by decide +kernel) (by decide)
def f27 : ℕ := 0x1001000a083007001f0
def s19 : List ℕ := [f0,f27,f2,f3,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof16 : Ban 40 6 s19 := viaCut rho1 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f28 : ℕ := 0xa005040a40e00f000f
def s20 : List ℕ := [f0,f28,f3,f10,f5,f4]
def rho4 : Projection 40 8 := pick [6,7,11,26,27,32,33,34] (by decide) (by decide) (by decide)
def f29 : ℕ := 0x91f
def f30 : ℕ := 0x50f8
def f31 : ℕ := 0xa6e7
def s21 : List ℕ := [f29,f30,f31]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w4 : Wide 8 3 s21 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof17 : Ban 40 6 s20 := viaCut rho4 w4 (by decide) (by decide +kernel) (by decide +kernel)
def s22 : List ℕ := [f0,f28,f2,f3,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof18 : Ban 40 6 s22 := viaSmall (by decide +kernel) (by decide)
def f32 : ℕ := 0x10844c8448308c4c0cc0
def s23 : List ℕ := [f2,f3,f32,f10,f5,f4]
def rho5 : Projection 40 8 := pick [0,1,2,12,13,14,16,17] (by decide) (by decide) (by decide)
def f33 : ℕ := 0x2d3f
def f34 : ℕ := 0x42c7
def f35 : ℕ := 0x90f8
def s24 : List ℕ := [f33,f34,f35]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w5 : Wide 8 3 s24 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof19 : Ban 40 6 s23 := viaCut rho5 w5 (by decide) (by decide +kernel) (by decide +kernel)
def s25 : List ℕ := [f0,f2,f3,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof20 : Ban 40 6 s25 := viaSmall (by decide +kernel) (by decide)
def s26 : List ℕ := [f0,f2,f3,f32,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof21 : Ban 40 6 s26 := viaSmall (by decide +kernel) (by decide)
def f36 : ℕ := 0x8004040800800c0e0f
def s27 : List ℕ := [f0,f36,f2,f3,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof22 : Ban 40 6 s27 := viaSmall (by decide +kernel) (by decide)
def f37 : ℕ := 0x14b5cddf5f7cffcfffff
def s28 : List ℕ := [f0,f2,f3,f10,f37,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof23 : Ban 40 6 s28 := viaSmall (by decide +kernel) (by decide)
def f38 : ℕ := 0x101548d155381f40f1f0
def s29 : List ℕ := [f0,f2,f3,f38,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof24 : Ban 40 6 s29 := viaSmall (by decide +kernel) (by decide)
def f39 : ℕ := 0x420810a024460830000
def s30 : List ℕ := [f0,f39,f2,f3,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof25 : Ban 40 6 s30 := viaSmall (by decide +kernel) (by decide)
def f40 : ℕ := 0x400ff0
def s31 : List ℕ := [f40,f0,f2,f3,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w6 : Wide 8 2 s10 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof26 : Ban 40 6 s31 := viaWeakCut rho2 w6 (by decide) (by decide +kernel) (by decide +kernel)
def f41 : ℕ := 0x1595dcdffdbf9ffcffff
def s32 : List ℕ := [f0,f2,f3,f10,f41,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof27 : Ban 40 6 s32 := viaSmall (by decide +kernel) (by decide)
def f42 : ℕ := 0x10954cd55d389f0cf00f
def s33 : List ℕ := [f0,f2,f3,f42,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof28 : Ban 40 6 s33 := viaWeakCut rho2 w6 (by decide) (by decide +kernel) (by decide +kernel)
def f43 : ℕ := 0x500900aa08700b00000
def s34 : List ℕ := [f0,f2,f43,f3,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof29 : Ban 40 6 s34 := viaSmall (by decide +kernel) (by decide)
def f44 : ℕ := 0x813000000
def s35 : List ℕ := [f44,f0,f2,f3,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof30 : Ban 40 6 s35 := viaCut rho1 w1 (by decide) (by decide +kernel) (by decide +kernel)
def f45 : ℕ := 0xea5b005115ffff00f33f
def s36 : List ℕ := [f2,f3,f10,f5,f45,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof31 : Ban 40 6 s36 := viaWeakCut rho2 w2 (by decide) (by decide +kernel) (by decide +kernel)
def s37 : List ℕ := [f0,f2,f3,f10,f5,f45,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof32 : Ban 40 6 s37 := viaCut rho1 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f46 : ℕ := 0xea4a000000f7ec000000
def s38 : List ℕ := [f0,f2,f3,f10,f46,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof33 : Ban 40 6 s38 := viaCut rho1 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f47 : ℕ := 0x11005115000000f33f
def s39 : List ℕ := [f47,f2,f3,f10,f5,f4]
def rho6 : Projection 40 7 := pick [6,7,25,26,27,32,33] (by decide) (by decide) (by decide)
def f48 : ℕ := 0x49f
def f49 : ℕ := 0x1163
def f50 : ℕ := 0x2a7c
def s40 : List ℕ := [f48,f49,f50]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w7 : Wide 7 3 s40 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof34 : Ban 40 6 s39 := viaCut rho6 w7 (by decide) (by decide +kernel) (by decide +kernel)
def s41 : List ℕ := [f47,f0,f2,f3,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof35 : Ban 40 6 s41 := viaSmall (by decide +kernel) (by decide)
def f51 : ℕ := 0x44e0000000
def s42 : List ℕ := [f51,f0,f2,f3,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof36 : Ban 40 6 s42 := viaCut rho1 w1 (by decide) (by decide +kernel) (by decide +kernel)
def f52 : ℕ := 0xeeea850e0affff8f0e0f
def s43 : List ℕ := [f0,f2,f3,f10,f5,f52,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof37 : Ban 40 6 s43 := viaSmall (by decide +kernel) (by decide)
def f53 : ℕ := 0xea4a000000bb1f000000
def s44 : List ℕ := [f0,f2,f3,f10,f53,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof38 : Ban 40 6 s44 := viaCut rho1 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f54 : ℕ := 0x4a0850e0a00008f0e0f
def s45 : List ℕ := [f0,f54,f2,f3,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof39 : Ban 40 6 s45 := viaSmall (by decide +kernel) (by decide)
def f55 : ℕ := 0x8700000000
def s46 : List ℕ := [f55,f0,f2,f3,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof40 : Ban 40 6 s46 := viaWeakCut rho2 w6 (by decide) (by decide +kernel) (by decide +kernel)
def f56 : ℕ := 0xef4a900aa0fffff00ff0
def s47 : List ℕ := [f0,f2,f3,f10,f5,f56,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof41 : Ban 40 6 s47 := viaWeakCut rho2 w6 (by decide) (by decide +kernel) (by decide +kernel)
def f57 : ℕ := 0xea4a00000078ff000000
def s48 : List ℕ := [f0,f2,f3,f10,f57,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof42 : Ban 40 6 s48 := viaWeakCut rho2 w6 (by decide) (by decide +kernel) (by decide +kernel)
def f58 : ℕ := 0x500900aa00000f00ff0
def s49 : List ℕ := [f0,f2,f58,f3,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof43 : Ban 40 6 s49 := viaWeakCut rho2 w6 (by decide) (by decide +kernel) (by decide +kernel)
def f59 : ℕ := 0x389f000000
def s50 : List ℕ := [f59,f0,f2,f3,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof44 : Ban 40 6 s50 := viaWeakCut rho2 w6 (by decide) (by decide +kernel) (by decide +kernel)
def f60 : ℕ := 0xfadf4cd55dffff4cffff
def s51 : List ℕ := [f0,f2,f3,f10,f5,f4,f60]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof45 : Ban 40 6 s51 := viaSmall (by decide +kernel) (by decide)
def f61 : ℕ := 0xea4a000000c760000000
def s52 : List ℕ := [f0,f2,f3,f10,f61,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof46 : Ban 40 6 s52 := viaSmall (by decide +kernel) (by decide)
def f62 : ℕ := 0x10954cd55d00004cffff
def s53 : List ℕ := [f0,f2,f3,f62,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof47 : Ban 40 6 s53 := viaWeakCut rho2 w6 (by decide) (by decide +kernel) (by decide +kernel)
def f63 : ℕ := 0x80000f000
def s54 : List ℕ := [f63,f0,f2,f3,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof48 : Ban 40 6 s54 := viaCut rho1 w1 (by decide) (by decide +kernel) (by decide +kernel)
def f64 : ℕ := 0xf8116af115f813fff33f
def s55 : List ℕ := [f0,f2,f3,f10,f5,f4,f64]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof49 : Ban 40 6 s55 := viaSmall (by decide +kernel) (by decide)
def f65 : ℕ := 0xf8006aa000f000ff0000
def s56 : List ℕ := [f0,f2,f3,f10,f5,f65,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof50 : Ban 40 6 s56 := viaSmall (by decide +kernel) (by decide)
def f66 : ℕ := 0x11005115001300033f
def s57 : List ℕ := [f66,f0,f2,f3,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof51 : Ban 40 6 s57 := viaSmall (by decide +kernel) (by decide)
def f67 : ℕ := 0x40008f0000
def s58 : List ℕ := [f67,f0,f2,f3,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof52 : Ban 40 6 s58 := viaCut rho1 w1 (by decide) (by decide +kernel) (by decide +kernel)
def f68 : ℕ := 0xfca0efae0afce0fffe0f
def s59 : List ℕ := [f0,f2,f3,f10,f5,f4,f68]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof53 : Ban 40 6 s59 := viaSmall (by decide +kernel) (by decide)
def f69 : ℕ := 0xf8006aa000b80070f000
def s60 : List ℕ := [f0,f2,f3,f10,f5,f69,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof54 : Ban 40 6 s60 := viaSmall (by decide +kernel) (by decide)
def f70 : ℕ := 0x4a0850e0a04e0000e0f
def s61 : List ℕ := [f0,f70,f2,f3,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof55 : Ban 40 6 s61 := viaSmall (by decide +kernel) (by decide)
def f71 : ℕ := 0x8000f00000
def s62 : List ℕ := [f71,f0,f2,f3,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof56 : Ban 40 6 s62 := viaCut rho1 w1 (by decide) (by decide +kernel) (by decide +kernel)
def f72 : ℕ := 0xfd00faaaa0ff00fffff0
def s63 : List ℕ := [f0,f2,f3,f10,f5,f4,f72]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof57 : Ban 40 6 s63 := viaSmall (by decide +kernel) (by decide)
def f73 : ℕ := 0xf8006aa00078000ff000
def s64 : List ℕ := [f0,f2,f3,f10,f5,f73,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof58 : Ban 40 6 s64 := viaSmall (by decide +kernel) (by decide)
def f74 : ℕ := 0x500900aa00700000ff0
def s65 : List ℕ := [f0,f2,f74,f3,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof59 : Ban 40 6 s65 := viaCut rho1 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f75 : ℕ := 0x100048800038004cf000
def s66 : List ℕ := [f0,f2,f3,f75,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof60 : Ban 40 6 s66 := viaSmall (by decide +kernel) (by decide)
def f76 : ℕ := 0xf8956ef55df89fffffff
def s67 : List ℕ := [f0,f2,f3,f10,f5,f4,f76]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof61 : Ban 40 6 s67 := viaSmall (by decide +kernel) (by decide)
def f77 : ℕ := 0xe800222000c000b30000
def s68 : List ℕ := [f0,f2,f3,f10,f77,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof62 : Ban 40 6 s68 := viaSmall (by decide +kernel) (by decide)
def f78 : ℕ := 0x9504555d009f000fff
def s69 : List ℕ := [f0,f78,f2,f3,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof63 : Ban 40 6 s69 := viaSmall (by decide +kernel) (by decide)
def f79 : ℕ := 0xe800000000f800000000
def s70 : List ℕ := [f0,f2,f3,f10,f79,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof64 : Ban 40 6 s70 := viaSmall (by decide +kernel) (by decide)
def f80 : ℕ := 0xfa4a6aa000fffffff000
def s71 : List ℕ := [f0,f2,f3,f10,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof65 : Ban 40 6 s71 := viaWeakCut rho2 w2 (by decide) (by decide +kernel) (by decide +kernel)
def s72 : List ℕ := [f0,f2,f3,f10,f5,f4,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof66 : Ban 40 6 s72 := viaSmall (by decide +kernel) (by decide)
def f81 : ℕ := 0x10006aa0000000fff000
def s73 : List ℕ := [f0,f2,f3,f81,f10,f5]
def rho7 : Projection 40 8 := pick [6,7,26,27,32,33,37,39] (by decide) (by decide) (by decide)
def f82 : ℕ := 0x54f
def f83 : ℕ := 0x12b3
def f84 : ℕ := 0xe8fc
def s74 : List ℕ := [f82,f83,f84]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w8 : Wide 8 3 s74 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof67 : Ban 40 6 s73 := viaCut rho7 w8 (by decide) (by decide +kernel) (by decide +kernel)
def s75 : List ℕ := [f0,f2,f3,f81,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof68 : Ban 40 6 s75 := viaSmall (by decide +kernel) (by decide)
def f85 : ℕ := 0x24a00000007ff000000
def s76 : List ℕ := [f0,f85,f2,f3,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof69 : Ban 40 6 s76 := viaCut rho1 w0 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof2 : Ban 40 7 s3 := viaBranch (ws := [s4,s5,s6,s7,s8,s9,s11,s12,s13,s15,s16,s17,s18,s19,s20,s22,s23,s25,s26,s27,s28,s29,s30,s31,s32,s33,s34,s35,s36,s37,s38,s39,s41,s42,s43,s44,s45,s46,s47,s48,s49,s50,s51,s52,s53,s54,s55,s56,s57,s58,s59,s60,s61,s62,s63,s64,s65,s66,s67,s68,s69,s70,s71,s72,s73,s75,s76])
  (consBan proof3 (consBan proof4 (consBan proof5 (consBan proof6 (consBan proof7 (consBan proof8 (consBan proof9 (consBan proof10 (consBan proof11 (consBan proof12 (consBan proof13 (consBan proof14 (consBan proof15 (consBan proof16 (consBan proof17 (consBan proof18 (consBan proof19 (consBan proof20 (consBan proof21 (consBan proof22 (consBan proof23 (consBan proof24 (consBan proof25 (consBan proof26 (consBan proof27 (consBan proof28 (consBan proof29 (consBan proof30 (consBan proof31 (consBan proof32 (consBan proof33 (consBan proof34 (consBan proof35 (consBan proof36 (consBan proof37 (consBan proof38 (consBan proof39 (consBan proof40 (consBan proof41 (consBan proof42 (consBan proof43 (consBan proof44 (consBan proof45 (consBan proof46 (consBan proof47 (consBan proof48 (consBan proof49 (consBan proof50 (consBan proof51 (consBan proof52 (consBan proof53 (consBan proof54 (consBan proof55 (consBan proof56 (consBan proof57 (consBan proof58 (consBan proof59 (consBan proof60 (consBan proof61 (consBan proof62 (consBan proof63 (consBan proof64 (consBan proof65 (consBan proof66 (consBan proof67 (consBan proof68 (consBan proof69 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def s77 : List ℕ := [f0,f2,f3,f1,f10,f5,f4]
def rho8 : Weak 40 6 := signedPick 2 [2,3,14,15,18,19] (by decide) (by decide) (by decide)
def f86 : ℕ := 0xb4c
def f87 : ℕ := 0xeb0
def s78 : List ℕ := [f9,f86,f87]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w9 : Wide 6 3 s78 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof70 : Ban 40 7 s77 := viaWeakCut rho8 w9 (by decide) (by decide +kernel) (by decide +kernel)
def s79 : List ℕ := [f11,f0,f2,f3,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof72 : Ban 40 6 s79 := viaCut rho1 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s80 : List ℕ := [f0,f2,f12,f3,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof73 : Ban 40 6 s80 := viaSmall (by decide +kernel) (by decide)
def s81 : List ℕ := [f0,f13,f2,f3,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof74 : Ban 40 6 s81 := viaSmall (by decide +kernel) (by decide)
def s82 : List ℕ := [f14,f0,f2,f3,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof75 : Ban 40 6 s82 := viaSmall (by decide +kernel) (by decide)
def s83 : List ℕ := [f15,f0,f2,f3,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof76 : Ban 40 6 s83 := viaCut rho1 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s84 : List ℕ := [f0,f2,f3,f16,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof77 : Ban 40 6 s84 := viaCut rho1 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s85 : List ℕ := [f0,f2,f20,f3,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof78 : Ban 40 6 s85 := viaSmall (by decide +kernel) (by decide)
def s86 : List ℕ := [f21,f0,f2,f3,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof79 : Ban 40 6 s86 := viaSmall (by decide +kernel) (by decide)
def s87 : List ℕ := [f0,f25,f2,f3,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof80 : Ban 40 6 s87 := viaSmall (by decide +kernel) (by decide)
def s88 : List ℕ := [f0,f3,f26,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof81 : Ban 40 6 s88 := viaCut rho5 w5 (by decide) (by decide +kernel) (by decide +kernel)
def s89 : List ℕ := [f0,f2,f3,f26,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof82 : Ban 40 6 s89 := viaSmall (by decide +kernel) (by decide)
def s90 : List ℕ := [f0,f27,f2,f3,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof83 : Ban 40 6 s90 := viaSmall (by decide +kernel) (by decide)
def s91 : List ℕ := [f0,f28,f3,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof84 : Ban 40 6 s91 := viaCut rho5 w5 (by decide) (by decide +kernel) (by decide +kernel)
def s92 : List ℕ := [f0,f28,f2,f3,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof85 : Ban 40 6 s92 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof86 : Ban 40 6 s3 := viaCut rho1 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f88 : ℕ := 0x8004040800800c0c00
def s93 : List ℕ := [f0,f88,f2,f3,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof87 : Ban 40 6 s93 := viaSmall (by decide +kernel) (by decide)
def f89 : ℕ := 0x14a4cd8e4a74eccf0ecf
def s94 : List ℕ := [f0,f2,f3,f32,f89,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof88 : Ban 40 6 s94 := viaSmall (by decide +kernel) (by decide)
def f90 : ℕ := 0x1004488040300c4000c0
def s95 : List ℕ := [f0,f2,f3,f90,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof89 : Ban 40 6 s95 := viaSmall (by decide +kernel) (by decide)
def f91 : ℕ := 0x420810a02446083020f
def s96 : List ℕ := [f0,f91,f2,f3,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof90 : Ban 40 6 s96 := viaSmall (by decide +kernel) (by decide)
def f92 : ℕ := 0x400cc0
def s97 : List ℕ := [f92,f0,f2,f3,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w10 : Wide 8 2 s24 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof91 : Ban 40 6 s97 := viaCut rho5 w10 (by decide) (by decide +kernel) (by decide +kernel)
def f93 : ℕ := 0x1584dc8ee8b78cfc0ff0
def s98 : List ℕ := [f0,f2,f3,f32,f93,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof92 : Ban 40 6 s98 := viaSmall (by decide +kernel) (by decide)
def f94 : ℕ := 0x10844c8448308c0c0000
def s99 : List ℕ := [f0,f2,f3,f94,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof93 : Ban 40 6 s99 := viaCut rho5 w10 (by decide) (by decide +kernel) (by decide +kernel)
def f95 : ℕ := 0x500900aa08700b00330
def s100 : List ℕ := [f0,f2,f95,f3,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof94 : Ban 40 6 s100 := viaSmall (by decide +kernel) (by decide)
def s101 : List ℕ := [f44,f0,f2,f3,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof95 : Ban 40 6 s101 := viaCut rho1 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s102 : List ℕ := [f0,f2,f3,f32,f5,f45,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof96 : Ban 40 6 s102 := viaCut rho1 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s103 : List ℕ := [f0,f2,f3,f32,f46,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof97 : Ban 40 6 s103 := viaSmall (by decide +kernel) (by decide)
def s104 : List ℕ := [f47,f0,f2,f3,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof98 : Ban 40 6 s104 := viaSmall (by decide +kernel) (by decide)
def s105 : List ℕ := [f51,f0,f2,f3,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof99 : Ban 40 6 s105 := viaCut rho1 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s106 : List ℕ := [f0,f2,f3,f32,f5,f52,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof100 : Ban 40 6 s106 := viaSmall (by decide +kernel) (by decide)
def s107 : List ℕ := [f0,f2,f3,f32,f53,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof101 : Ban 40 6 s107 := viaSmall (by decide +kernel) (by decide)
def s108 : List ℕ := [f0,f54,f2,f3,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof102 : Ban 40 6 s108 := viaSmall (by decide +kernel) (by decide)
def s109 : List ℕ := [f55,f0,f2,f3,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof103 : Ban 40 6 s109 := viaCut rho5 w10 (by decide) (by decide +kernel) (by decide +kernel)
def s110 : List ℕ := [f0,f2,f3,f32,f5,f56,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof104 : Ban 40 6 s110 := viaCut rho5 w10 (by decide) (by decide +kernel) (by decide +kernel)
def s111 : List ℕ := [f0,f2,f3,f32,f57,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof105 : Ban 40 6 s111 := viaSmall (by decide +kernel) (by decide)
def s112 : List ℕ := [f0,f2,f58,f3,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof106 : Ban 40 6 s112 := viaSmall (by decide +kernel) (by decide)
def f96 : ℕ := 0x308c000000
def s113 : List ℕ := [f96,f0,f2,f3,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof107 : Ban 40 6 s113 := viaCut rho5 w10 (by decide) (by decide +kernel) (by decide +kernel)
def f97 : ℕ := 0xface4c8448ffff4c0cc0
def s114 : List ℕ := [f0,f2,f3,f32,f5,f4,f97]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof108 : Ban 40 6 s114 := viaSmall (by decide +kernel) (by decide)
def f98 : ℕ := 0xea4a000000cf73000000
def s115 : List ℕ := [f0,f2,f3,f32,f98,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof109 : Ban 40 6 s115 := viaSmall (by decide +kernel) (by decide)
def f99 : ℕ := 0x10844c844800004c0cc0
def s116 : List ℕ := [f0,f2,f3,f99,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof110 : Ban 40 6 s116 := viaCut rho5 w10 (by decide) (by decide +kernel) (by decide +kernel)
def s117 : List ℕ := [f63,f0,f2,f3,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof111 : Ban 40 6 s117 := viaCut rho1 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s118 : List ℕ := [f0,f2,f3,f32,f5,f4,f64]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof112 : Ban 40 6 s118 := viaSmall (by decide +kernel) (by decide)
def s119 : List ℕ := [f0,f2,f3,f32,f5,f65,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof113 : Ban 40 6 s119 := viaSmall (by decide +kernel) (by decide)
def s120 : List ℕ := [f66,f0,f2,f3,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof114 : Ban 40 6 s120 := viaSmall (by decide +kernel) (by decide)
def s121 : List ℕ := [f67,f0,f2,f3,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof115 : Ban 40 6 s121 := viaCut rho1 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s122 : List ℕ := [f0,f2,f3,f32,f5,f4,f68]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof116 : Ban 40 6 s122 := viaSmall (by decide +kernel) (by decide)
def s123 : List ℕ := [f0,f2,f3,f32,f5,f69,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof117 : Ban 40 6 s123 := viaSmall (by decide +kernel) (by decide)
def s124 : List ℕ := [f0,f70,f2,f3,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof118 : Ban 40 6 s124 := viaSmall (by decide +kernel) (by decide)
def s125 : List ℕ := [f71,f0,f2,f3,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof119 : Ban 40 6 s125 := viaCut rho1 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s126 : List ℕ := [f0,f2,f3,f32,f5,f4,f72]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof120 : Ban 40 6 s126 := viaSmall (by decide +kernel) (by decide)
def s127 : List ℕ := [f0,f2,f3,f32,f5,f73,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof121 : Ban 40 6 s127 := viaSmall (by decide +kernel) (by decide)
def s128 : List ℕ := [f0,f2,f74,f3,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof122 : Ban 40 6 s128 := viaSmall (by decide +kernel) (by decide)
def f100 : ℕ := 0x100048800030004c0000
def s129 : List ℕ := [f0,f2,f3,f100,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof123 : Ban 40 6 s129 := viaSmall (by decide +kernel) (by decide)
def f101 : ℕ := 0xf8846ea448f88cfffcc0
def s130 : List ℕ := [f0,f2,f3,f32,f5,f4,f101]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof124 : Ban 40 6 s130 := viaSmall (by decide +kernel) (by decide)
def f102 : ℕ := 0xe800222000c800b3f000
def s131 : List ℕ := [f0,f2,f3,f32,f102,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof125 : Ban 40 6 s131 := viaSmall (by decide +kernel) (by decide)
def f103 : ℕ := 0x84040448008c000cc0
def s132 : List ℕ := [f0,f103,f2,f3,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof126 : Ban 40 6 s132 := viaSmall (by decide +kernel) (by decide)
def s133 : List ℕ := [f0,f2,f3,f32,f79,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof127 : Ban 40 6 s133 := viaSmall (by decide +kernel) (by decide)
def s134 : List ℕ := [f0,f2,f3,f32,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof128 : Ban 40 6 s134 := viaCut rho5 w5 (by decide) (by decide +kernel) (by decide +kernel)
def s135 : List ℕ := [f0,f2,f3,f32,f5,f4,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof129 : Ban 40 6 s135 := viaSmall (by decide +kernel) (by decide)
def s136 : List ℕ := [f0,f2,f3,f81,f32,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof130 : Ban 40 6 s136 := viaCut rho5 w5 (by decide) (by decide +kernel) (by decide +kernel)
def s137 : List ℕ := [f0,f2,f3,f81,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof131 : Ban 40 6 s137 := viaSmall (by decide +kernel) (by decide)
def s138 : List ℕ := [f0,f85,f2,f3,f32,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof132 : Ban 40 6 s138 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof71 : Ban 40 7 s25 := viaBranch (ws := [s79,s80,s81,s82,s83,s84,s85,s86,s87,s88,s89,s90,s91,s92,s23,s3,s26,s93,s94,s95,s96,s97,s98,s99,s100,s101,s102,s103,s104,s105,s106,s107,s108,s109,s110,s111,s112,s113,s114,s115,s116,s117,s118,s119,s120,s121,s122,s123,s124,s125,s126,s127,s128,s129,s130,s131,s132,s133,s134,s135,s136,s137,s138])
  (consBan proof72 (consBan proof73 (consBan proof74 (consBan proof75 (consBan proof76 (consBan proof77 (consBan proof78 (consBan proof79 (consBan proof80 (consBan proof81 (consBan proof82 (consBan proof83 (consBan proof84 (consBan proof85 (consBan proof19 (consBan proof86 (consBan proof21 (consBan proof87 (consBan proof88 (consBan proof89 (consBan proof90 (consBan proof91 (consBan proof92 (consBan proof93 (consBan proof94 (consBan proof95 (consBan proof96 (consBan proof97 (consBan proof98 (consBan proof99 (consBan proof100 (consBan proof101 (consBan proof102 (consBan proof103 (consBan proof104 (consBan proof105 (consBan proof106 (consBan proof107 (consBan proof108 (consBan proof109 (consBan proof110 (consBan proof111 (consBan proof112 (consBan proof113 (consBan proof114 (consBan proof115 (consBan proof116 (consBan proof117 (consBan proof118 (consBan proof119 (consBan proof120 (consBan proof121 (consBan proof122 (consBan proof123 (consBan proof124 (consBan proof125 (consBan proof126 (consBan proof127 (consBan proof128 (consBan proof129 (consBan proof130 (consBan proof131 (consBan proof132 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def s139 : List ℕ := [f0,f2,f3,f32,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof133 : Ban 40 7 s139 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f104 : ℕ := 0x10010110803003233
def s140 : List ℕ := [f104,f0,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof134 : Ban 40 7 s140 := viaCut rho1 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s141 : List ℕ := [f11,f0,f2,f3,f1,f5,f4]
def rho9 : Projection 40 6 := pick [4,5,12,13,20,21] (by decide) (by decide) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof135 : Ban 40 7 s141 := viaCut rho9 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s142 : List ℕ := [f0,f2,f12,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof136 : Ban 40 7 s142 := viaCut rho1 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s143 : List ℕ := [f0,f13,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof137 : Ban 40 7 s143 := viaCut rho9 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s144 : List ℕ := [f14,f0,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof138 : Ban 40 7 s144 := viaCut rho1 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f105 : ℕ := 0x8004040800800c0c0c
def s145 : List ℕ := [f0,f105,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof139 : Ban 40 7 s145 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f106 : ℕ := 0x14b4cdcf4e74fccfcfcf
def s146 : List ℕ := [f0,f2,f3,f1,f106,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof140 : Ban 40 7 s146 := viaCut rho9 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f107 : ℕ := 0x420810a024460830203
def s147 : List ℕ := [f0,f107,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof141 : Ban 40 7 s147 := viaCut rho9 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f108 : ℕ := 0x101448c144301c40c1c0
def s148 : List ℕ := [f0,f2,f3,f108,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof142 : Ban 40 7 s148 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s149 : List ℕ := [f15,f0,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof143 : Ban 40 7 s149 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s150 : List ℕ := [f0,f2,f3,f16,f1,f5,f4]
def s151 : List ℕ := [f15,f2,f16,f1,f5,f4]
def rho10 : Projection 40 9 := pick [0,1,12,13,16,17,20,21,23] (by decide) (by decide) (by decide)
def f109 : ℕ := 0x151fc
def f110 : ℕ := 0x22533
def f111 : ℕ := 0x28bcf
def s152 : List ℕ := [f109,f110,f111]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w11 : Wide 9 3 s152 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof145 : Ban 40 6 s151 := viaCut rho10 w11 (by decide) (by decide +kernel) (by decide +kernel)
def s153 : List ℕ := [f15,f2,f3,f16,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof146 : Ban 40 6 s153 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s154 : List ℕ := [f15,f0,f2,f16,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof147 : Ban 40 6 s154 := viaCut rho1 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s155 : List ℕ := [f2,f20,f3,f16,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof148 : Ban 40 6 s155 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s156 : List ℕ := [f21,f0,f2,f16,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof149 : Ban 40 6 s156 := viaCut rho1 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s157 : List ℕ := [f0,f16,f26,f1,f5,f4]
def rho11 : Projection 40 23 := pick [0,1,2,3,4,5,6,7,8,9,10,11,24,25,26,27,28,29,30,31,32,33,34] (by decide) (by decide) (by decide)
def f112 : ℕ := 0x888a81333f
def f113 : ℕ := 0x4a2a609cdcc
def f114 : ℕ := 0x1250007ff000
def f115 : ℕ := 0x288ddaf13fff
def f116 : ℕ := 0x2d07557e0fff
def s158 : List ℕ := [f112,f113,f114,f115,f116]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w12 : Wide 23 5 s158 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof150 : Ban 40 6 s157 := viaCut rho11 w12 (by decide) (by decide +kernel) (by decide +kernel)
def s159 : List ℕ := [f0,f3,f16,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof151 : Ban 40 6 s159 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s160 : List ℕ := [f0,f2,f16,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof152 : Ban 40 6 s160 := viaCut rho1 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s161 : List ℕ := [f0,f27,f2,f16,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof153 : Ban 40 6 s161 := viaSmall (by decide +kernel) (by decide)
def s162 : List ℕ := [f0,f28,f3,f16,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof154 : Ban 40 6 s162 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s163 : List ℕ := [f0,f2,f20,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof155 : Ban 40 6 s163 := viaSmall (by decide +kernel) (by decide)
def f117 : ℕ := 0x400800a000400800e0f
def s164 : List ℕ := [f0,f117,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof156 : Ban 40 6 s164 := viaSmall (by decide +kernel) (by decide)
def f118 : ℕ := 0x5b1955fbfcff3ffffff
def s165 : List ℕ := [f0,f2,f3,f118,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof157 : Ban 40 6 s165 := viaSmall (by decide +kernel) (by decide)
def f119 : ℕ := 0x1111051b58b1370f1f0
def s166 : List ℕ := [f0,f119,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof158 : Ban 40 6 s166 := viaSmall (by decide +kernel) (by decide)
def f120 : ℕ := 0xa005040a40e00f0000
def s167 : List ℕ := [f0,f120,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof159 : Ban 40 6 s167 := viaSmall (by decide +kernel) (by decide)
def s168 : List ℕ := [f21,f0,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof160 : Ban 40 6 s168 := viaSmall (by decide +kernel) (by decide)
def s169 : List ℕ := [f2,f3,f16,f1,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof161 : Ban 40 6 s169 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s170 : List ℕ := [f104,f2,f3,f16,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof162 : Ban 40 6 s170 := viaSmall (by decide +kernel) (by decide)
def f121 : ℕ := 0x10004104001040cdcc
def s171 : List ℕ := [f121,f0,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof163 : Ban 40 6 s171 := viaSmall (by decide +kernel) (by decide)
def s172 : List ℕ := [f0,f2,f3,f1,f41,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof164 : Ban 40 6 s172 := viaSmall (by decide +kernel) (by decide)
def s173 : List ℕ := [f0,f2,f3,f94,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof165 : Ban 40 6 s173 := viaSmall (by decide +kernel) (by decide)
def f122 : ℕ := 0x501901ab18f03b03233
def s174 : List ℕ := [f0,f2,f3,f122,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof166 : Ban 40 6 s174 := viaSmall (by decide +kernel) (by decide)
def s175 : List ℕ := [f2,f3,f16,f1,f5,f45,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof167 : Ban 40 6 s175 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s176 : List ℕ := [f47,f2,f3,f16,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof168 : Ban 40 6 s176 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s177 : List ℕ := [f0,f2,f16,f1,f5,f56,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof169 : Ban 40 6 s177 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s178 : List ℕ := [f0,f2,f58,f16,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof170 : Ban 40 6 s178 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f123 : ℕ := 0x8f13000000
def s179 : List ℕ := [f123,f0,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof171 : Ban 40 6 s179 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def f124 : ℕ := 0xef5b905bb5fffff0ffff
def s180 : List ℕ := [f0,f2,f3,f1,f5,f124,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof172 : Ban 40 6 s180 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f125 : ℕ := 0xea4a00000070ec000000
def s181 : List ℕ := [f0,f2,f3,f1,f125,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof173 : Ban 40 6 s181 := viaSmall (by decide +kernel) (by decide)
def f126 : ℕ := 0x511905bb50000f0ffff
def s182 : List ℕ := [f0,f2,f3,f126,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof174 : Ban 40 6 s182 := viaSmall (by decide +kernel) (by decide)
def s183 : List ℕ := [f2,f3,f16,f1,f5,f4,f64]
def rho12 : Projection 40 6 := pick [0,1,24,25,29,30] (by decide) (by decide) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof175 : Ban 40 6 s183 := viaCut rho12 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s184 : List ℕ := [f66,f2,f3,f16,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof176 : Ban 40 6 s184 := viaCut rho12 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s185 : List ℕ := [f0,f2,f16,f1,f5,f4,f72]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof177 : Ban 40 6 s185 := viaCut rho12 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s186 : List ℕ := [f0,f2,f74,f16,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof178 : Ban 40 6 s186 := viaCut rho12 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f127 : ℕ := 0x8800f0f000
def s187 : List ℕ := [f127,f0,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof179 : Ban 40 6 s187 := viaCut rho12 w1 (by decide) (by decide +kernel) (by decide +kernel)
def f128 : ℕ := 0xfd11fafbb5ff13ffffff
def s188 : List ℕ := [f0,f2,f3,f1,f5,f4,f128]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof180 : Ban 40 6 s188 := viaSmall (by decide +kernel) (by decide)
def f129 : ℕ := 0xf8006aa00070000f0000
def s189 : List ℕ := [f0,f2,f3,f1,f5,f129,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof181 : Ban 40 6 s189 := viaSmall (by decide +kernel) (by decide)
def f130 : ℕ := 0x511905bb50713000fff
def s190 : List ℕ := [f0,f2,f3,f130,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof182 : Ban 40 6 s190 := viaSmall (by decide +kernel) (by decide)
def s191 : List ℕ := [f0,f2,f3,f16,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof183 : Ban 40 6 s191 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s192 : List ℕ := [f0,f2,f3,f16,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof184 : Ban 40 6 s192 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof144 : Ban 40 7 s150 := viaBranch (ws := [s151,s153,s154,s155,s156,s157,s159,s160,s161,s162,s163,s164,s165,s166,s167,s168,s9,s169,s11,s84,s170,s171,s172,s173,s174,s175,s176,s177,s178,s179,s180,s181,s182,s183,s184,s185,s186,s187,s188,s189,s190,s191,s192])
  (consBan proof145 (consBan proof146 (consBan proof147 (consBan proof148 (consBan proof149 (consBan proof150 (consBan proof151 (consBan proof152 (consBan proof153 (consBan proof154 (consBan proof155 (consBan proof156 (consBan proof157 (consBan proof158 (consBan proof159 (consBan proof160 (consBan proof8 (consBan proof161 (consBan proof9 (consBan proof77 (consBan proof162 (consBan proof163 (consBan proof164 (consBan proof165 (consBan proof166 (consBan proof167 (consBan proof168 (consBan proof169 (consBan proof170 (consBan proof171 (consBan proof172 (consBan proof173 (consBan proof174 (consBan proof175 (consBan proof176 (consBan proof177 (consBan proof178 (consBan proof179 (consBan proof180 (consBan proof181 (consBan proof182 (consBan proof183 (consBan proof184 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof185 : Ban 40 7 s163 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof186 : Ban 40 7 s168 := viaCut rho1 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f131 : ℕ := 0x400dc0
def s193 : List ℕ := [f131,f0,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof187 : Ban 40 7 s193 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f132 : ℕ := 0x1594dccfecb79cfccffc
def s194 : List ℕ := [f0,f2,f3,f1,f132,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof188 : Ban 40 7 s194 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f133 : ℕ := 0x500900aa08700b00230
def s195 : List ℕ := [f0,f2,f133,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof189 : Ban 40 7 s195 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f134 : ℕ := 0x10944cc54c309c0cc00c
def s196 : List ℕ := [f0,f2,f3,f134,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof190 : Ban 40 7 s196 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s197 : List ℕ := [f0,f25,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof191 : Ban 40 7 s197 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s198 : List ℕ := [f0,f3,f26,f1,f5,f4]
def s199 : List ℕ := [f15,f0,f3,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof193 : Ban 40 6 s199 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s200 : List ℕ := [f0,f20,f26,f1,f5,f4]
def rho13 : Projection 40 7 := pick [0,1,4,12,13,16,17] (by decide) (by decide) (by decide)
def f135 : ℕ := 0x69f
def f136 : ℕ := 0x1167
def s201 : List ℕ := [f135,f136,f24]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w13 : Wide 7 3 s201 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof194 : Ban 40 6 s200 := viaCut rho13 w13 (by decide) (by decide +kernel) (by decide +kernel)
def s202 : List ℕ := [f0,f20,f3,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof195 : Ban 40 6 s202 := viaSmall (by decide +kernel) (by decide)
def s203 : List ℕ := [f21,f0,f3,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof196 : Ban 40 6 s203 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f137 : ℕ := 0x33f
def s204 : List ℕ := [f137,f0,f3,f26,f1,f5,f4]
def rho14 : Projection 40 12 := pick [6,7,10,11,26,27,29,30,31,32,33,34] (by decide) (by decide) (by decide)
def f138 : ℕ := 0x11513f
def f139 : ℕ := 0x4a0ff0
def f140 : ℕ := 0xa0ae0f
def f141 : ℕ := 0xb4efcf
def s205 : List ℕ := [f138,f139,f140,f141]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w14 : Wide 12 3 s205 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof197 : Ban 40 6 s204 := viaCut rho14 w14 (by decide) (by decide +kernel) (by decide +kernel)
def s206 : List ℕ := [f0,f3,f26,f118,f1,f5,f4]
def f142 : ℕ := 0x280550700ff0
def f143 : ℕ := 0x2d8fdfff3fff
def s207 : List ℕ := [f112,f113,f114,f142,f116,f143]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w15 : Wide 23 5 s207 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof198 : Ban 40 6 s206 := viaCut rho11 w15 (by decide) (by decide +kernel) (by decide +kernel)
def f144 : ℕ := 0x5a0950eaac7e0ff0cc0
def s208 : List ℕ := [f0,f3,f144,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof199 : Ban 40 6 s208 := viaSmall (by decide +kernel) (by decide)
def f145 : ℕ := 0x11005115081300f000
def s209 : List ℕ := [f145,f0,f3,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof200 : Ban 40 6 s209 := viaSmall (by decide +kernel) (by decide)
def s210 : List ℕ := [f0,f28,f26,f1,f5,f4]
def rho15 : Projection 40 8 := pick [4,5,9,12,13,20,21,23] (by decide) (by decide) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof201 : Ban 40 6 s210 := viaCut rho15 w4 (by decide) (by decide +kernel) (by decide +kernel)
def s211 : List ℕ := [f0,f28,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof202 : Ban 40 6 s211 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s212 : List ℕ := [f0,f28,f3,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof203 : Ban 40 6 s212 := viaSmall (by decide +kernel) (by decide)
def s213 : List ℕ := [f6,f0,f3,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof204 : Ban 40 6 s213 := viaSmall (by decide +kernel) (by decide)
def s214 : List ℕ := [f0,f3,f26,f1,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof205 : Ban 40 6 s214 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s215 : List ℕ := [f0,f3,f26,f32,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof206 : Ban 40 6 s215 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s216 : List ℕ := [f104,f0,f3,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof207 : Ban 40 6 s216 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s217 : List ℕ := [f131,f0,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof208 : Ban 40 6 s217 := viaWeakCut rho8 w9 (by decide) (by decide +kernel) (by decide +kernel)
def s218 : List ℕ := [f131,f0,f3,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof209 : Ban 40 6 s218 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s219 : List ℕ := [f0,f3,f26,f1,f132,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof210 : Ban 40 6 s219 := viaSmall (by decide +kernel) (by decide)
def s220 : List ℕ := [f0,f26,f134,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof211 : Ban 40 6 s220 := viaWeakCut rho8 w9 (by decide) (by decide +kernel) (by decide +kernel)
def s221 : List ℕ := [f0,f3,f26,f134,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof212 : Ban 40 6 s221 := viaSmall (by decide +kernel) (by decide)
def s222 : List ℕ := [f0,f133,f3,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof213 : Ban 40 6 s222 := viaSmall (by decide +kernel) (by decide)
def f146 : ℕ := 0x8004040800804c0dcc
def s223 : List ℕ := [f0,f146,f3,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof214 : Ban 40 6 s223 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def f147 : ℕ := 0x15b4ddcfeef7fcffcfff
def s224 : List ℕ := [f0,f3,f26,f1,f147,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof215 : Ban 40 6 s224 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f148 : ℕ := 0x101448c144301c00c000
def s225 : List ℕ := [f0,f3,f26,f148,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof216 : Ban 40 6 s225 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def f149 : ℕ := 0x520910aa2c760b30233
def s226 : List ℕ := [f0,f3,f149,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof217 : Ban 40 6 s226 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s227 : List ℕ := [f44,f0,f3,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof218 : Ban 40 6 s227 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s228 : List ℕ := [f0,f3,f26,f1,f5,f45,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof219 : Ban 40 6 s228 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s229 : List ℕ := [f0,f3,f26,f1,f46,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof220 : Ban 40 6 s229 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s230 : List ℕ := [f47,f0,f3,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof221 : Ban 40 6 s230 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s231 : List ℕ := [f55,f0,f3,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof222 : Ban 40 6 s231 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s232 : List ℕ := [f0,f26,f1,f5,f56,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof223 : Ban 40 6 s232 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s233 : List ℕ := [f0,f3,f26,f1,f5,f56,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof224 : Ban 40 6 s233 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s234 : List ℕ := [f0,f3,f26,f1,f57,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof225 : Ban 40 6 s234 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s235 : List ℕ := [f0,f58,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof226 : Ban 40 6 s235 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s236 : List ℕ := [f0,f58,f3,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof227 : Ban 40 6 s236 := viaSmall (by decide +kernel) (by decide)
def f150 : ℕ := 0xc7e0000000
def s237 : List ℕ := [f150,f0,f3,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof228 : Ban 40 6 s237 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def f151 : ℕ := 0xefea950eaaffffff0fff
def s238 : List ℕ := [f0,f3,f26,f1,f5,f151,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof229 : Ban 40 6 s238 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f152 : ℕ := 0xea4a000000381f000000
def s239 : List ℕ := [f0,f3,f26,f1,f152,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof230 : Ban 40 6 s239 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def f153 : ℕ := 0x5a0950eaa0000ff0fff
def s240 : List ℕ := [f0,f3,f153,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof231 : Ban 40 6 s240 := viaSmall (by decide +kernel) (by decide)
def f154 : ℕ := 0x309c000000
def s241 : List ℕ := [f154,f0,f3,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof232 : Ban 40 6 s241 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def f155 : ℕ := 0xfade4cc54cffff4ccdcc
def s242 : List ℕ := [f0,f3,f26,f1,f5,f4,f155]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof233 : Ban 40 6 s242 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def f156 : ℕ := 0xea4a000000cf63000000
def s243 : List ℕ := [f0,f3,f26,f1,f156,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof234 : Ban 40 6 s243 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def f157 : ℕ := 0x10944cc54c00004ccdcc
def s244 : List ℕ := [f0,f3,f26,f157,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof235 : Ban 40 6 s244 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s245 : List ℕ := [f63,f0,f3,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof236 : Ban 40 6 s245 := viaCut rho12 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s246 : List ℕ := [f0,f3,f26,f1,f5,f4,f64]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof237 : Ban 40 6 s246 := viaCut rho12 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s247 : List ℕ := [f0,f3,f26,f1,f5,f65,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof238 : Ban 40 6 s247 := viaSmall (by decide +kernel) (by decide)
def s248 : List ℕ := [f66,f0,f3,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof239 : Ban 40 6 s248 := viaCut rho12 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s249 : List ℕ := [f71,f0,f3,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof240 : Ban 40 6 s249 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s250 : List ℕ := [f0,f26,f1,f5,f4,f72]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof241 : Ban 40 6 s250 := viaCut rho12 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s251 : List ℕ := [f0,f3,f26,f1,f5,f4,f72]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof242 : Ban 40 6 s251 := viaSmall (by decide +kernel) (by decide)
def s252 : List ℕ := [f0,f3,f26,f1,f5,f73,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof243 : Ban 40 6 s252 := viaSmall (by decide +kernel) (by decide)
def s253 : List ℕ := [f0,f74,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof244 : Ban 40 6 s253 := viaCut rho12 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s254 : List ℕ := [f0,f74,f3,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof245 : Ban 40 6 s254 := viaSmall (by decide +kernel) (by decide)
def f158 : ℕ := 0xc000ff0000
def s255 : List ℕ := [f158,f0,f3,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof246 : Ban 40 6 s255 := viaCut rho12 w1 (by decide) (by decide +kernel) (by decide +kernel)
def f159 : ℕ := 0xfda0ffaeaaffe0ffffff
def s256 : List ℕ := [f0,f3,f26,f1,f5,f4,f159]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof247 : Ban 40 6 s256 := viaSmall (by decide +kernel) (by decide)
def f160 : ℕ := 0xf8006aa000380000f000
def s257 : List ℕ := [f0,f3,f26,f1,f5,f160,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof248 : Ban 40 6 s257 := viaSmall (by decide +kernel) (by decide)
def f161 : ℕ := 0x5a0950eaa07e0000fff
def s258 : List ℕ := [f0,f3,f161,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof249 : Ban 40 6 s258 := viaSmall (by decide +kernel) (by decide)
def f162 : ℕ := 0x100048800030004cc000
def s259 : List ℕ := [f0,f3,f26,f162,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof250 : Ban 40 6 s259 := viaSmall (by decide +kernel) (by decide)
def f163 : ℕ := 0xf8946ee54cf89cfffdcc
def s260 : List ℕ := [f0,f3,f26,f1,f5,f4,f163]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof251 : Ban 40 6 s260 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f164 : ℕ := 0xe800222000c800b33000
def s261 : List ℕ := [f0,f3,f26,f1,f164,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof252 : Ban 40 6 s261 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f165 : ℕ := 0x9404454c009c000dcc
def s262 : List ℕ := [f0,f165,f3,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof253 : Ban 40 6 s262 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s263 : List ℕ := [f0,f3,f26,f1,f79,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof254 : Ban 40 6 s263 := viaSmall (by decide +kernel) (by decide)
def s264 : List ℕ := [f0,f3,f26,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof255 : Ban 40 6 s264 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s265 : List ℕ := [f0,f3,f26,f1,f5,f4,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof256 : Ban 40 6 s265 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s266 : List ℕ := [f0,f3,f26,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof257 : Ban 40 6 s266 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s267 : List ℕ := [f0,f3,f26,f81,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof258 : Ban 40 6 s267 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s268 : List ℕ := [f0,f85,f3,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof259 : Ban 40 6 s268 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof192 : Ban 40 7 s198 := viaBranch (ws := [s199,s157,s159,s200,s202,s203,s204,s206,s208,s209,s210,s211,s212,s213,s17,s214,s88,s215,s216,s217,s218,s219,s220,s221,s222,s223,s224,s225,s226,s227,s228,s229,s230,s231,s232,s233,s234,s235,s236,s237,s238,s239,s240,s241,s242,s243,s244,s245,s246,s247,s248,s249,s250,s251,s252,s253,s254,s255,s256,s257,s258,s259,s260,s261,s262,s263,s264,s265,s266,s267,s268])
  (consBan proof193 (consBan proof150 (consBan proof151 (consBan proof194 (consBan proof195 (consBan proof196 (consBan proof197 (consBan proof198 (consBan proof199 (consBan proof200 (consBan proof201 (consBan proof202 (consBan proof203 (consBan proof204 (consBan proof14 (consBan proof205 (consBan proof81 (consBan proof206 (consBan proof207 (consBan proof208 (consBan proof209 (consBan proof210 (consBan proof211 (consBan proof212 (consBan proof213 (consBan proof214 (consBan proof215 (consBan proof216 (consBan proof217 (consBan proof218 (consBan proof219 (consBan proof220 (consBan proof221 (consBan proof222 (consBan proof223 (consBan proof224 (consBan proof225 (consBan proof226 (consBan proof227 (consBan proof228 (consBan proof229 (consBan proof230 (consBan proof231 (consBan proof232 (consBan proof233 (consBan proof234 (consBan proof235 (consBan proof236 (consBan proof237 (consBan proof238 (consBan proof239 (consBan proof240 (consBan proof241 (consBan proof242 (consBan proof243 (consBan proof244 (consBan proof245 (consBan proof246 (consBan proof247 (consBan proof248 (consBan proof249 (consBan proof250 (consBan proof251 (consBan proof252 (consBan proof253 (consBan proof254 (consBan proof255 (consBan proof256 (consBan proof257 (consBan proof258 (consBan proof259 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def s269 : List ℕ := [f0,f2,f3,f26,f1,f5,f4]
def s270 : List ℕ := [f11,f0,f3,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof261 : Ban 40 6 s270 := viaSmall (by decide +kernel) (by decide)
def s271 : List ℕ := [f0,f12,f3,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof262 : Ban 40 6 s271 := viaSmall (by decide +kernel) (by decide)
def s272 : List ℕ := [f0,f13,f3,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof263 : Ban 40 6 s272 := viaSmall (by decide +kernel) (by decide)
def s273 : List ℕ := [f14,f0,f3,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof264 : Ban 40 6 s273 := viaSmall (by decide +kernel) (by decide)
def s274 : List ℕ := [f0,f2,f20,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof265 : Ban 40 6 s274 := viaSmall (by decide +kernel) (by decide)
def s275 : List ℕ := [f0,f25,f26,f1,f5,f4]
def rho16 : Projection 40 9 := pick [6,7,26,27,29,30,31,32,33] (by decide) (by decide) (by decide)
def f166 : ℕ := 0x8a4f
def f167 : ℕ := 0x1a5f3
def f168 : ℕ := 0x251fc
def s276 : List ℕ := [f166,f167,f168]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w16 : Wide 9 3 s276 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof266 : Ban 40 6 s275 := viaCut rho16 w16 (by decide) (by decide +kernel) (by decide +kernel)
def s277 : List ℕ := [f0,f25,f3,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof267 : Ban 40 6 s277 := viaSmall (by decide +kernel) (by decide)
def s278 : List ℕ := [f0,f25,f2,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof268 : Ban 40 6 s278 := viaSmall (by decide +kernel) (by decide)
def s279 : List ℕ := [f0,f27,f3,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof269 : Ban 40 6 s279 := viaSmall (by decide +kernel) (by decide)
def s280 : List ℕ := [f0,f28,f2,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof270 : Ban 40 6 s280 := viaSmall (by decide +kernel) (by decide)
def s281 : List ℕ := [f137,f0,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof271 : Ban 40 6 s281 := viaCut rho1 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s282 : List ℕ := [f0,f2,f3,f144,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof272 : Ban 40 6 s282 := viaSmall (by decide +kernel) (by decide)
def s283 : List ℕ := [f145,f0,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof273 : Ban 40 6 s283 := viaSmall (by decide +kernel) (by decide)
def s284 : List ℕ := [f0,f27,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof274 : Ban 40 6 s284 := viaSmall (by decide +kernel) (by decide)
def s285 : List ℕ := [f0,f28,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof275 : Ban 40 6 s285 := viaSmall (by decide +kernel) (by decide)
def s286 : List ℕ := [f0,f105,f3,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof276 : Ban 40 6 s286 := viaSmall (by decide +kernel) (by decide)
def s287 : List ℕ := [f0,f3,f26,f1,f106,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof277 : Ban 40 6 s287 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s288 : List ℕ := [f0,f3,f26,f108,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof278 : Ban 40 6 s288 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s289 : List ℕ := [f0,f107,f3,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof279 : Ban 40 6 s289 := viaSmall (by decide +kernel) (by decide)
def s290 : List ℕ := [f131,f0,f2,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof280 : Ban 40 6 s290 := viaCut rho9 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s291 : List ℕ := [f0,f2,f26,f134,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof281 : Ban 40 6 s291 := viaSmall (by decide +kernel) (by decide)
def s292 : List ℕ := [f0,f146,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof282 : Ban 40 6 s292 := viaSmall (by decide +kernel) (by decide)
def s293 : List ℕ := [f0,f2,f3,f1,f147,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof283 : Ban 40 6 s293 := viaSmall (by decide +kernel) (by decide)
def s294 : List ℕ := [f0,f2,f3,f148,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof284 : Ban 40 6 s294 := viaSmall (by decide +kernel) (by decide)
def s295 : List ℕ := [f0,f2,f3,f149,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof285 : Ban 40 6 s295 := viaSmall (by decide +kernel) (by decide)
def s296 : List ℕ := [f51,f0,f3,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof286 : Ban 40 6 s296 := viaSmall (by decide +kernel) (by decide)
def s297 : List ℕ := [f0,f3,f26,f1,f5,f52,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof287 : Ban 40 6 s297 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s298 : List ℕ := [f0,f3,f26,f1,f53,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof288 : Ban 40 6 s298 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s299 : List ℕ := [f0,f54,f3,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof289 : Ban 40 6 s299 := viaSmall (by decide +kernel) (by decide)
def s300 : List ℕ := [f0,f2,f26,f1,f5,f56,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof290 : Ban 40 6 s300 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s301 : List ℕ := [f0,f2,f58,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof291 : Ban 40 6 s301 := viaSmall (by decide +kernel) (by decide)
def s302 : List ℕ := [f150,f0,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof292 : Ban 40 6 s302 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s303 : List ℕ := [f0,f2,f3,f1,f5,f151,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof293 : Ban 40 6 s303 := viaSmall (by decide +kernel) (by decide)
def s304 : List ℕ := [f0,f2,f3,f1,f152,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof294 : Ban 40 6 s304 := viaSmall (by decide +kernel) (by decide)
def s305 : List ℕ := [f0,f2,f3,f153,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof295 : Ban 40 6 s305 := viaSmall (by decide +kernel) (by decide)
def s306 : List ℕ := [f67,f0,f3,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof296 : Ban 40 6 s306 := viaSmall (by decide +kernel) (by decide)
def s307 : List ℕ := [f0,f3,f26,f1,f5,f4,f68]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof297 : Ban 40 6 s307 := viaSmall (by decide +kernel) (by decide)
def s308 : List ℕ := [f0,f3,f26,f1,f5,f69,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof298 : Ban 40 6 s308 := viaSmall (by decide +kernel) (by decide)
def s309 : List ℕ := [f0,f70,f3,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof299 : Ban 40 6 s309 := viaSmall (by decide +kernel) (by decide)
def s310 : List ℕ := [f0,f2,f26,f1,f5,f4,f72]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof300 : Ban 40 6 s310 := viaSmall (by decide +kernel) (by decide)
def s311 : List ℕ := [f0,f2,f74,f26,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof301 : Ban 40 6 s311 := viaSmall (by decide +kernel) (by decide)
def s312 : List ℕ := [f158,f0,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof302 : Ban 40 6 s312 := viaCut rho12 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s313 : List ℕ := [f0,f2,f3,f1,f5,f4,f159]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof303 : Ban 40 6 s313 := viaSmall (by decide +kernel) (by decide)
def s314 : List ℕ := [f0,f2,f3,f1,f5,f160,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof304 : Ban 40 6 s314 := viaSmall (by decide +kernel) (by decide)
def s315 : List ℕ := [f0,f2,f3,f161,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof305 : Ban 40 6 s315 := viaSmall (by decide +kernel) (by decide)
def s316 : List ℕ := [f0,f2,f3,f26,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof306 : Ban 40 6 s316 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s317 : List ℕ := [f0,f2,f3,f26,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof307 : Ban 40 6 s317 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof260 : Ban 40 7 s269 := viaBranch (ws := [s270,s271,s272,s273,s160,s274,s275,s277,s278,s279,s210,s212,s280,s281,s165,s282,s283,s284,s285,s18,s89,s286,s287,s288,s289,s290,s291,s292,s293,s294,s295,s296,s297,s298,s299,s300,s301,s302,s303,s304,s305,s306,s307,s308,s309,s310,s311,s312,s313,s314,s315,s316,s317])
  (consBan proof261 (consBan proof262 (consBan proof263 (consBan proof264 (consBan proof152 (consBan proof265 (consBan proof266 (consBan proof267 (consBan proof268 (consBan proof269 (consBan proof201 (consBan proof203 (consBan proof270 (consBan proof271 (consBan proof157 (consBan proof272 (consBan proof273 (consBan proof274 (consBan proof275 (consBan proof15 (consBan proof82 (consBan proof276 (consBan proof277 (consBan proof278 (consBan proof279 (consBan proof280 (consBan proof281 (consBan proof282 (consBan proof283 (consBan proof284 (consBan proof285 (consBan proof286 (consBan proof287 (consBan proof288 (consBan proof289 (consBan proof290 (consBan proof291 (consBan proof292 (consBan proof293 (consBan proof294 (consBan proof295 (consBan proof296 (consBan proof297 (consBan proof298 (consBan proof299 (consBan proof300 (consBan proof301 (consBan proof302 (consBan proof303 (consBan proof304 (consBan proof305 (consBan proof306 (consBan proof307 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof308 : Ban 40 7 s284 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f169 : ℕ := 0xf
def s318 : List ℕ := [f169,f0,f28,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w17 : Wide 8 2 s21 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof310 : Ban 40 6 s318 := viaCut rho15 w17 (by decide) (by decide +kernel) (by decide +kernel)
def f170 : ℕ := 0xb105551f48f30ff33f
def s319 : List ℕ := [f0,f28,f170,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof311 : Ban 40 6 s319 := viaCut rho15 w4 (by decide) (by decide +kernel) (by decide +kernel)
def s320 : List ℕ := [f0,f120,f28,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof312 : Ban 40 6 s320 := viaCut rho15 w17 (by decide) (by decide +kernel) (by decide +kernel)
def f171 : ℕ := 0x11005115081300f330
def s321 : List ℕ := [f171,f0,f28,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof313 : Ban 40 6 s321 := viaSmall (by decide +kernel) (by decide)
def s322 : List ℕ := [f15,f0,f28,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof314 : Ban 40 6 s322 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s323 : List ℕ := [f0,f28,f20,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof315 : Ban 40 6 s323 := viaSmall (by decide +kernel) (by decide)
def s324 : List ℕ := [f21,f0,f28,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof316 : Ban 40 6 s324 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof317 : Ban 40 6 s198 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s325 : List ℕ := [f6,f0,f28,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof318 : Ban 40 6 s325 := viaSmall (by decide +kernel) (by decide)
def s326 : List ℕ := [f0,f28,f3,f1,f10,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof319 : Ban 40 6 s326 := viaSmall (by decide +kernel) (by decide)
def s327 : List ℕ := [f0,f28,f3,f32,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof320 : Ban 40 6 s327 := viaSmall (by decide +kernel) (by decide)
def s328 : List ℕ := [f104,f0,f28,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof321 : Ban 40 6 s328 := viaSmall (by decide +kernel) (by decide)
def f172 : ℕ := 0x8004040800800c000c
def s329 : List ℕ := [f0,f172,f28,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof322 : Ban 40 6 s329 := viaSmall (by decide +kernel) (by decide)
def f173 : ℕ := 0x10b44dc54e70fc4fcdcf
def s330 : List ℕ := [f0,f28,f3,f173,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof323 : Ban 40 6 s330 := viaCut rho15 w4 (by decide) (by decide +kernel) (by decide +kernel)
def s331 : List ℕ := [f0,f28,f3,f1,f173,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof324 : Ban 40 6 s331 := viaSmall (by decide +kernel) (by decide)
def f174 : ℕ := 0x101448c144301c40cdc0
def s332 : List ℕ := [f0,f28,f3,f174,f5,f4]
def rho17 : Projection 40 8 := pick [0,1,3,12,13,16,17,18] (by decide) (by decide) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof325 : Ban 40 6 s332 := viaCut rho17 w4 (by decide) (by decide +kernel) (by decide +kernel)
def s333 : List ℕ := [f0,f28,f3,f174,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof326 : Ban 40 6 s333 := viaSmall (by decide +kernel) (by decide)
def f175 : ℕ := 0x200100024060030003
def s334 : List ℕ := [f0,f175,f28,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof327 : Ban 40 6 s334 := viaSmall (by decide +kernel) (by decide)
def s335 : List ℕ := [f131,f0,f28,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof328 : Ban 40 6 s335 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s336 : List ℕ := [f0,f28,f3,f1,f132,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof329 : Ban 40 6 s336 := viaSmall (by decide +kernel) (by decide)
def s337 : List ℕ := [f0,f28,f3,f134,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof330 : Ban 40 6 s337 := viaSmall (by decide +kernel) (by decide)
def s338 : List ℕ := [f0,f28,f133,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof331 : Ban 40 6 s338 := viaSmall (by decide +kernel) (by decide)
def s339 : List ℕ := [f44,f0,f28,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof332 : Ban 40 6 s339 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s340 : List ℕ := [f0,f28,f3,f1,f5,f45,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof333 : Ban 40 6 s340 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s341 : List ℕ := [f0,f28,f3,f1,f46,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof334 : Ban 40 6 s341 := viaSmall (by decide +kernel) (by decide)
def s342 : List ℕ := [f47,f0,f28,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof335 : Ban 40 6 s342 := viaSmall (by decide +kernel) (by decide)
def f176 : ℕ := 0x40e0000000
def s343 : List ℕ := [f176,f0,f28,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof336 : Ban 40 6 s343 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def f177 : ℕ := 0xeaea05040affff0f000f
def s344 : List ℕ := [f0,f28,f3,f1,f5,f177,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof337 : Ban 40 6 s344 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f178 : ℕ := 0xea4a000000bf1f000000
def s345 : List ℕ := [f0,f28,f3,f1,f178,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof338 : Ban 40 6 s345 := viaSmall (by decide +kernel) (by decide)
def f179 : ℕ := 0xa005040a00000f000f
def s346 : List ℕ := [f0,f179,f28,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof339 : Ban 40 6 s346 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s347 : List ℕ := [f55,f0,f28,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof340 : Ban 40 6 s347 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s348 : List ℕ := [f0,f28,f3,f1,f5,f56,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof341 : Ban 40 6 s348 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s349 : List ℕ := [f0,f28,f3,f1,f57,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof342 : Ban 40 6 s349 := viaSmall (by decide +kernel) (by decide)
def s350 : List ℕ := [f0,f28,f58,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof343 : Ban 40 6 s350 := viaSmall (by decide +kernel) (by decide)
def s351 : List ℕ := [f154,f0,f28,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof344 : Ban 40 6 s351 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s352 : List ℕ := [f0,f28,f3,f1,f5,f4,f155]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof345 : Ban 40 6 s352 := viaSmall (by decide +kernel) (by decide)
def s353 : List ℕ := [f0,f28,f3,f1,f156,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof346 : Ban 40 6 s353 := viaSmall (by decide +kernel) (by decide)
def s354 : List ℕ := [f0,f28,f3,f157,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof347 : Ban 40 6 s354 := viaSmall (by decide +kernel) (by decide)
def s355 : List ℕ := [f63,f0,f28,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof348 : Ban 40 6 s355 := viaCut rho12 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s356 : List ℕ := [f0,f28,f3,f1,f5,f4,f64]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof349 : Ban 40 6 s356 := viaSmall (by decide +kernel) (by decide)
def s357 : List ℕ := [f0,f28,f3,f1,f5,f65,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof350 : Ban 40 6 s357 := viaSmall (by decide +kernel) (by decide)
def s358 : List ℕ := [f66,f0,f28,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof351 : Ban 40 6 s358 := viaSmall (by decide +kernel) (by decide)
def f180 : ℕ := 0x40000f0000
def s359 : List ℕ := [f180,f0,f28,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof352 : Ban 40 6 s359 := viaCut rho12 w1 (by decide) (by decide +kernel) (by decide +kernel)
def f181 : ℕ := 0xf8a06fa40af8e0fff00f
def s360 : List ℕ := [f0,f28,f3,f1,f5,f4,f181]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof353 : Ban 40 6 s360 := viaSmall (by decide +kernel) (by decide)
def f182 : ℕ := 0xf8006aa000b800f0f000
def s361 : List ℕ := [f0,f28,f3,f1,f5,f182,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof354 : Ban 40 6 s361 := viaSmall (by decide +kernel) (by decide)
def f183 : ℕ := 0xa005040a00e000000f
def s362 : List ℕ := [f0,f183,f28,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof355 : Ban 40 6 s362 := viaCut rho12 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s363 : List ℕ := [f71,f0,f28,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof356 : Ban 40 6 s363 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s364 : List ℕ := [f0,f28,f3,f1,f5,f4,f72]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof357 : Ban 40 6 s364 := viaSmall (by decide +kernel) (by decide)
def s365 : List ℕ := [f0,f28,f3,f1,f5,f73,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof358 : Ban 40 6 s365 := viaSmall (by decide +kernel) (by decide)
def s366 : List ℕ := [f0,f28,f74,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof359 : Ban 40 6 s366 := viaSmall (by decide +kernel) (by decide)
def s367 : List ℕ := [f0,f28,f3,f162,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof360 : Ban 40 6 s367 := viaSmall (by decide +kernel) (by decide)
def s368 : List ℕ := [f0,f28,f3,f1,f5,f4,f163]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof361 : Ban 40 6 s368 := viaSmall (by decide +kernel) (by decide)
def s369 : List ℕ := [f0,f28,f3,f1,f164,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof362 : Ban 40 6 s369 := viaSmall (by decide +kernel) (by decide)
def s370 : List ℕ := [f0,f165,f28,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof363 : Ban 40 6 s370 := viaSmall (by decide +kernel) (by decide)
def s371 : List ℕ := [f0,f28,f3,f1,f79,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof364 : Ban 40 6 s371 := viaSmall (by decide +kernel) (by decide)
def s372 : List ℕ := [f0,f28,f3,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof365 : Ban 40 6 s372 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s373 : List ℕ := [f0,f28,f3,f1,f5,f4,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof366 : Ban 40 6 s373 := viaSmall (by decide +kernel) (by decide)
def s374 : List ℕ := [f0,f28,f3,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof367 : Ban 40 6 s374 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s375 : List ℕ := [f0,f28,f3,f81,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof368 : Ban 40 6 s375 := viaSmall (by decide +kernel) (by decide)
def s376 : List ℕ := [f0,f28,f85,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof369 : Ban 40 6 s376 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof309 : Ban 40 7 s211 := viaBranch (ws := [s318,s319,s320,s321,s322,s162,s323,s324,s198,s210,s212,s325,s20,s326,s91,s327,s328,s329,s330,s331,s332,s333,s334,s335,s336,s337,s338,s339,s340,s341,s342,s343,s344,s345,s346,s347,s348,s349,s350,s351,s352,s353,s354,s355,s356,s357,s358,s359,s360,s361,s362,s363,s364,s365,s366,s367,s368,s369,s370,s371,s372,s373,s374,s375,s376])
  (consBan proof310 (consBan proof311 (consBan proof312 (consBan proof313 (consBan proof314 (consBan proof154 (consBan proof315 (consBan proof316 (consBan proof317 (consBan proof201 (consBan proof203 (consBan proof318 (consBan proof17 (consBan proof319 (consBan proof84 (consBan proof320 (consBan proof321 (consBan proof322 (consBan proof323 (consBan proof324 (consBan proof325 (consBan proof326 (consBan proof327 (consBan proof328 (consBan proof329 (consBan proof330 (consBan proof331 (consBan proof332 (consBan proof333 (consBan proof334 (consBan proof335 (consBan proof336 (consBan proof337 (consBan proof338 (consBan proof339 (consBan proof340 (consBan proof341 (consBan proof342 (consBan proof343 (consBan proof344 (consBan proof345 (consBan proof346 (consBan proof347 (consBan proof348 (consBan proof349 (consBan proof350 (consBan proof351 (consBan proof352 (consBan proof353 (consBan proof354 (consBan proof355 (consBan proof356 (consBan proof357 (consBan proof358 (consBan proof359 (consBan proof360 (consBan proof361 (consBan proof362 (consBan proof363 (consBan proof364 (consBan proof365 (consBan proof366 (consBan proof367 (consBan proof368 (consBan proof369 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof370 : Ban 40 7 s285 := viaCut rho9 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s377 : List ℕ := [f63,f0,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof371 : Ban 40 7 s377 := viaCut rho12 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s378 : List ℕ := [f0,f2,f3,f1,f5,f4,f64]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof372 : Ban 40 7 s378 := viaCut rho1 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s379 : List ℕ := [f0,f2,f3,f1,f5,f65,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof373 : Ban 40 7 s379 := viaCut rho12 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s380 : List ℕ := [f66,f0,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof374 : Ban 40 7 s380 := viaCut rho1 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s381 : List ℕ := [f0,f2,f3,f162,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof375 : Ban 40 7 s381 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s382 : List ℕ := [f0,f2,f3,f1,f5,f4,f163]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof376 : Ban 40 7 s382 := viaCut rho12 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s383 : List ℕ := [f0,f2,f3,f1,f164,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof377 : Ban 40 7 s383 := viaCut rho12 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s384 : List ℕ := [f0,f165,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof378 : Ban 40 7 s384 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s385 : List ℕ := [f67,f0,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof379 : Ban 40 7 s385 := viaCut rho12 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s386 : List ℕ := [f0,f2,f3,f1,f5,f4,f68]
def rho18 : Projection 40 6 := pick [4,5,24,25,32,33] (by decide) (by decide) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof380 : Ban 40 7 s386 := viaCut rho18 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s387 : List ℕ := [f0,f2,f3,f1,f5,f69,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof381 : Ban 40 7 s387 := viaCut rho12 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s388 : List ℕ := [f0,f70,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof382 : Ban 40 7 s388 := viaCut rho9 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s389 : List ℕ := [f71,f0,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof383 : Ban 40 7 s389 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s390 : List ℕ := [f0,f2,f3,f1,f5,f4,f72]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof384 : Ban 40 7 s390 := viaCut rho12 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s391 : List ℕ := [f0,f2,f3,f1,f5,f73,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof385 : Ban 40 7 s391 := viaCut rho12 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s392 : List ℕ := [f0,f2,f74,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof386 : Ban 40 7 s392 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s393 : List ℕ := [f44,f0,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof387 : Ban 40 7 s393 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s394 : List ℕ := [f0,f2,f3,f1,f5,f45,f4]
def s395 : List ℕ := [f2,f12,f3,f1,f5,f45,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof389 : Ban 40 6 s395 := viaCut rho9 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s396 : List ℕ := [f14,f2,f3,f1,f5,f45,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof390 : Ban 40 6 s396 := viaCut rho9 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s397 : List ℕ := [f21,f2,f3,f1,f5,f45,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof391 : Ban 40 6 s397 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s398 : List ℕ := [f2,f3,f1,f10,f5,f45,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof392 : Ban 40 6 s398 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s399 : List ℕ := [f104,f2,f3,f1,f5,f45,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof393 : Ban 40 6 s399 := viaSmall (by decide +kernel) (by decide)
def s400 : List ℕ := [f44,f2,f3,f1,f45,f4]
def rho19 : Projection 40 9 := pick [0,1,12,13,16,17,29,30,38] (by decide) (by decide) (by decide)
def f184 : ℕ := 0xa5f3
def f185 : ℕ := 0x2513c
def f186 : ℕ := 0x30bcf
def s401 : List ℕ := [f184,f185,f186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w18 : Wide 9 3 s401 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof394 : Ban 40 6 s400 := viaCut rho19 w18 (by decide) (by decide +kernel) (by decide +kernel)
def s402 : List ℕ := [f44,f2,f3,f1,f5,f45,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof395 : Ban 40 6 s402 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s403 : List ℕ := [f44,f0,f2,f3,f1,f45,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof396 : Ban 40 6 s403 := viaCut rho1 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s404 : List ℕ := [f2,f3,f1,f46,f5,f45,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof397 : Ban 40 6 s404 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s405 : List ℕ := [f47,f0,f2,f3,f1,f45,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof398 : Ban 40 6 s405 := viaCut rho1 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s406 : List ℕ := [f0,f2,f3,f1,f45,f52,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof399 : Ban 40 6 s406 := viaCut rho9 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s407 : List ℕ := [f0,f2,f3,f1,f53,f45,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof400 : Ban 40 6 s407 := viaCut rho9 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s408 : List ℕ := [f0,f2,f3,f1,f45,f56,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof401 : Ban 40 6 s408 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s409 : List ℕ := [f0,f2,f3,f1,f57,f45,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof402 : Ban 40 6 s409 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s410 : List ℕ := [f0,f2,f3,f1,f46,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof403 : Ban 40 6 s410 := viaSmall (by decide +kernel) (by decide)
def f187 : ℕ := 0x44e000020f
def s411 : List ℕ := [f187,f0,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof404 : Ban 40 6 s411 := viaCut rho9 w1 (by decide) (by decide +kernel) (by decide +kernel)
def f188 : ℕ := 0xeefb855f1fffff8fff3f
def s412 : List ℕ := [f0,f2,f3,f1,f5,f188,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof405 : Ban 40 6 s412 := viaSmall (by decide +kernel) (by decide)
def f189 : ℕ := 0xea5b005115bb1f00f130
def s413 : List ℕ := [f0,f2,f3,f1,f5,f189,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof406 : Ban 40 6 s413 := viaSmall (by decide +kernel) (by decide)
def f190 : ℕ := 0x4a0850e0a00008f0c00
def s414 : List ℕ := [f0,f190,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof407 : Ban 40 6 s414 := viaSmall (by decide +kernel) (by decide)
def f191 : ℕ := 0x8700000330
def s415 : List ℕ := [f191,f0,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof408 : Ban 40 6 s415 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def f192 : ℕ := 0xea5b00511578ff00f00f
def s416 : List ℕ := [f0,f2,f3,f1,f5,f192,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof409 : Ban 40 6 s416 := viaSmall (by decide +kernel) (by decide)
def f193 : ℕ := 0x500900aa00000f00cc0
def s417 : List ℕ := [f0,f2,f193,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof410 : Ban 40 6 s417 := viaSmall (by decide +kernel) (by decide)
def f194 : ℕ := 0x10004104309c00c10c
def s418 : List ℕ := [f194,f0,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof411 : Ban 40 6 s418 := viaSmall (by decide +kernel) (by decide)
def s419 : List ℕ := [f0,f2,f3,f1,f5,f4,f60]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof412 : Ban 40 6 s419 := viaSmall (by decide +kernel) (by decide)
def f195 : ℕ := 0xea4b001011cf63003233
def s420 : List ℕ := [f0,f2,f3,f1,f5,f195,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof413 : Ban 40 6 s420 := viaSmall (by decide +kernel) (by decide)
def s421 : List ℕ := [f0,f2,f3,f99,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof414 : Ban 40 6 s421 := viaSmall (by decide +kernel) (by decide)
def s422 : List ℕ := [f47,f0,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof415 : Ban 40 6 s422 := viaSmall (by decide +kernel) (by decide)
def s423 : List ℕ := [f0,f2,f3,f1,f45,f80]
def rho20 : Projection 40 23 := pick [4,5,6,7,8,12,13,14,15,20,21,22,24,25,26,27,28,32,33,35,36,37,39] (by decide) (by decide) (by decide)
def f196 : ℕ := 0x88588931f3
def f197 : ℕ := 0x10105460e1f
def f198 : ℕ := 0x8a4ca31c99c
def f199 : ℕ := 0x36d858fff1f3
def f200 : ℕ := 0x3e56a07fffe0
def s424 : List ℕ := [f196,f197,f198,f199,f200]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w19 : Wide 23 5 s424 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof416 : Ban 40 6 s423 := viaCut rho20 w19 (by decide) (by decide +kernel) (by decide +kernel)
def s425 : List ℕ := [f0,f2,f3,f1,f45,f4,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof417 : Ban 40 6 s425 := viaCut rho1 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s426 : List ℕ := [f0,f2,f3,f1,f5,f45,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof418 : Ban 40 6 s426 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s427 : List ℕ := [f0,f2,f3,f81,f1,f5,f45]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof419 : Ban 40 6 s427 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s428 : List ℕ := [f0,f85,f2,f3,f1,f45,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof420 : Ban 40 6 s428 := viaSmall (by decide +kernel) (by decide)
def f201 : ℕ := 0xe800000000f80000f000
def s429 : List ℕ := [f0,f2,f3,f1,f201,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof421 : Ban 40 6 s429 := viaSmall (by decide +kernel) (by decide)
def f202 : ℕ := 0xfa5b6af115fffffff33f
def s430 : List ℕ := [f0,f2,f3,f1,f5,f4,f202]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof422 : Ban 40 6 s430 := viaSmall (by decide +kernel) (by decide)
def f203 : ℕ := 0x10006aa0000000ff0000
def s431 : List ℕ := [f0,f2,f3,f203,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof423 : Ban 40 6 s431 := viaSmall (by decide +kernel) (by decide)
def f204 : ℕ := 0x25b00511507ff00033f
def s432 : List ℕ := [f0,f204,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof424 : Ban 40 6 s432 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof388 : Ban 40 7 s394 := viaBranch (ws := [s395,s396,s175,s397,s228,s340,s36,s398,s37,s102,s399,s400,s402,s403,s404,s405,s406,s407,s408,s409,s410,s411,s412,s413,s414,s415,s180,s416,s417,s418,s419,s420,s421,s422,s423,s425,s426,s427,s428,s429,s430,s431,s432])
  (consBan proof389 (consBan proof390 (consBan proof167 (consBan proof391 (consBan proof219 (consBan proof333 (consBan proof31 (consBan proof392 (consBan proof32 (consBan proof96 (consBan proof393 (consBan proof394 (consBan proof395 (consBan proof396 (consBan proof397 (consBan proof398 (consBan proof399 (consBan proof400 (consBan proof401 (consBan proof402 (consBan proof403 (consBan proof404 (consBan proof405 (consBan proof406 (consBan proof407 (consBan proof408 (consBan proof172 (consBan proof409 (consBan proof410 (consBan proof411 (consBan proof412 (consBan proof413 (consBan proof414 (consBan proof415 (consBan proof416 (consBan proof417 (consBan proof418 (consBan proof419 (consBan proof420 (consBan proof421 (consBan proof422 (consBan proof423 (consBan proof424 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof425 : Ban 40 7 s410 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof426 : Ban 40 7 s422 := viaCut rho1 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s433 : List ℕ := [f154,f0,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof427 : Ban 40 7 s433 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s434 : List ℕ := [f0,f2,f3,f1,f5,f4,f155]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof428 : Ban 40 7 s434 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s435 : List ℕ := [f0,f2,f3,f1,f156,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof429 : Ban 40 7 s435 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s436 : List ℕ := [f0,f2,f3,f157,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof430 : Ban 40 7 s436 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s437 : List ℕ := [f51,f0,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof431 : Ban 40 7 s437 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s438 : List ℕ := [f0,f2,f3,f1,f5,f52,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof432 : Ban 40 7 s438 := viaCut rho9 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s439 : List ℕ := [f0,f2,f3,f1,f53,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof433 : Ban 40 7 s439 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s440 : List ℕ := [f0,f54,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof434 : Ban 40 7 s440 := viaCut rho9 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s441 : List ℕ := [f55,f0,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof435 : Ban 40 7 s441 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s442 : List ℕ := [f0,f2,f3,f1,f5,f56,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof436 : Ban 40 7 s442 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s443 : List ℕ := [f0,f2,f3,f1,f57,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof437 : Ban 40 7 s443 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s444 : List ℕ := [f0,f2,f58,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof438 : Ban 40 7 s444 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s445 : List ℕ := [f0,f2,f3,f1,f79,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof439 : Ban 40 7 s445 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s446 : List ℕ := [f0,f2,f3,f1,f5,f80]
def s447 : List ℕ := [f11,f0,f2,f3,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof441 : Ban 40 6 s447 := viaCut rho9 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s448 : List ℕ := [f0,f2,f12,f3,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof442 : Ban 40 6 s448 := viaCut rho9 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s449 : List ℕ := [f0,f13,f2,f3,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof443 : Ban 40 6 s449 := viaSmall (by decide +kernel) (by decide)
def s450 : List ℕ := [f14,f0,f2,f3,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof444 : Ban 40 6 s450 := viaCut rho9 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s451 : List ℕ := [f15,f0,f2,f3,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof445 : Ban 40 6 s451 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s452 : List ℕ := [f0,f2,f20,f3,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof446 : Ban 40 6 s452 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s453 : List ℕ := [f21,f0,f2,f3,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof447 : Ban 40 6 s453 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s454 : List ℕ := [f0,f25,f2,f3,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof448 : Ban 40 6 s454 := viaSmall (by decide +kernel) (by decide)
def s455 : List ℕ := [f0,f27,f2,f3,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof449 : Ban 40 6 s455 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s456 : List ℕ := [f0,f28,f2,f3,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof450 : Ban 40 6 s456 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s457 : List ℕ := [f6,f0,f2,f3,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof451 : Ban 40 6 s457 := viaSmall (by decide +kernel) (by decide)
def s458 : List ℕ := [f0,f2,f3,f1,f10,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof452 : Ban 40 6 s458 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s459 : List ℕ := [f0,f2,f3,f32,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof453 : Ban 40 6 s459 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s460 : List ℕ := [f104,f0,f2,f3,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof454 : Ban 40 6 s460 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s461 : List ℕ := [f0,f105,f2,f3,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof455 : Ban 40 6 s461 := viaSmall (by decide +kernel) (by decide)
def s462 : List ℕ := [f0,f2,f3,f1,f106,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof456 : Ban 40 6 s462 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s463 : List ℕ := [f0,f2,f3,f108,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof457 : Ban 40 6 s463 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s464 : List ℕ := [f0,f107,f2,f3,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof458 : Ban 40 6 s464 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s465 : List ℕ := [f131,f0,f2,f3,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof459 : Ban 40 6 s465 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s466 : List ℕ := [f0,f2,f3,f1,f132,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof460 : Ban 40 6 s466 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s467 : List ℕ := [f0,f2,f3,f134,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof461 : Ban 40 6 s467 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s468 : List ℕ := [f0,f2,f133,f3,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof462 : Ban 40 6 s468 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s469 : List ℕ := [f44,f0,f2,f3,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof463 : Ban 40 6 s469 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s470 : List ℕ := [f0,f2,f3,f1,f46,f80]
def rho21 : Projection 40 7 := pick [0,1,12,13,16,17,24] (by decide) (by decide) (by decide)
def f205 : ℕ := 0x933
def f206 : ℕ := 0x147c
def f207 : ℕ := 0x22cf
def s471 : List ℕ := [f205,f206,f207]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w20 : Wide 7 3 s471 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof464 : Ban 40 6 s470 := viaCut rho21 w20 (by decide) (by decide +kernel) (by decide +kernel)
def s472 : List ℕ := [f0,f2,f3,f1,f46,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof465 : Ban 40 6 s472 := viaSmall (by decide +kernel) (by decide)
def s473 : List ℕ := [f47,f0,f2,f3,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof466 : Ban 40 6 s473 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s474 : List ℕ := [f51,f0,f2,f3,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof467 : Ban 40 6 s474 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s475 : List ℕ := [f0,f2,f3,f1,f52,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof468 : Ban 40 6 s475 := viaCut rho9 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s476 : List ℕ := [f0,f2,f3,f1,f5,f52,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof469 : Ban 40 6 s476 := viaSmall (by decide +kernel) (by decide)
def s477 : List ℕ := [f0,f2,f3,f1,f53,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof470 : Ban 40 6 s477 := viaCut rho9 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s478 : List ℕ := [f0,f2,f3,f1,f53,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof471 : Ban 40 6 s478 := viaSmall (by decide +kernel) (by decide)
def s479 : List ℕ := [f0,f54,f2,f3,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof472 : Ban 40 6 s479 := viaSmall (by decide +kernel) (by decide)
def s480 : List ℕ := [f55,f0,f2,f3,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof473 : Ban 40 6 s480 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s481 : List ℕ := [f0,f2,f3,f1,f56,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof474 : Ban 40 6 s481 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s482 : List ℕ := [f0,f2,f3,f1,f5,f56,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof475 : Ban 40 6 s482 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s483 : List ℕ := [f0,f2,f3,f1,f57,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof476 : Ban 40 6 s483 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s484 : List ℕ := [f0,f2,f3,f1,f57,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof477 : Ban 40 6 s484 := viaSmall (by decide +kernel) (by decide)
def s485 : List ℕ := [f0,f2,f58,f3,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof478 : Ban 40 6 s485 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s486 : List ℕ := [f154,f0,f2,f3,f1,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof479 : Ban 40 6 s486 := viaWeakCut rho8 w9 (by decide) (by decide +kernel) (by decide +kernel)
def s487 : List ℕ := [f154,f0,f2,f3,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof480 : Ban 40 6 s487 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s488 : List ℕ := [f0,f2,f3,f1,f5,f80,f155]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof481 : Ban 40 6 s488 := viaSmall (by decide +kernel) (by decide)
def s489 : List ℕ := [f0,f2,f3,f1,f156,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof482 : Ban 40 6 s489 := viaSmall (by decide +kernel) (by decide)
def s490 : List ℕ := [f0,f2,f3,f157,f1,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof483 : Ban 40 6 s490 := viaWeakCut rho8 w9 (by decide) (by decide +kernel) (by decide +kernel)
def s491 : List ℕ := [f0,f2,f3,f157,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof484 : Ban 40 6 s491 := viaSmall (by decide +kernel) (by decide)
def f208 : ℕ := 0x81300f000
def s492 : List ℕ := [f208,f0,f2,f3,f1,f5,f80]
def rho22 : Projection 40 12 := pick [0,1,2,3,4,5,6,7,8,9,10,11] (by decide) (by decide) (by decide)
def f209 : ℕ := 0x11533f
def f210 : ℕ := 0x54cdcc
def f211 : ℕ := 0xaa0ff0
def f212 : ℕ := 0xe0ae0f
def s493 : List ℕ := [f209,f210,f211,f212]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w21 : Wide 12 3 s493 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof485 : Ban 40 6 s492 := viaCut rho22 w21 (by decide) (by decide +kernel) (by decide +kernel)
def s494 : List ℕ := [f0,f2,f3,f1,f5,f80,f202]
def f213 : ℕ := 0x3650007ff000
def f214 : ℕ := 0x3edef8fffff3
def s495 : List ℕ := [f196,f197,f198,f213,f200,f214]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w22 : Wide 23 5 s495 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof486 : Ban 40 6 s494 := viaCut rho20 w22 (by decide) (by decide +kernel) (by decide +kernel)
def f215 : ℕ := 0xfa4a6aa000f7ecff0000
def s496 : List ℕ := [f0,f2,f3,f1,f5,f215,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof487 : Ban 40 6 s496 := viaSmall (by decide +kernel) (by decide)
def f216 : ℕ := 0x11005115000000033f
def s497 : List ℕ := [f216,f0,f2,f3,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof488 : Ban 40 6 s497 := viaSmall (by decide +kernel) (by decide)
def f217 : ℕ := 0x44e08f0000
def s498 : List ℕ := [f217,f0,f2,f3,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof489 : Ban 40 6 s498 := viaCut rho9 w1 (by decide) (by decide +kernel) (by decide +kernel)
def f218 : ℕ := 0xfeeaefae0afffffffe0f
def s499 : List ℕ := [f0,f2,f3,f1,f5,f80,f218]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof490 : Ban 40 6 s499 := viaSmall (by decide +kernel) (by decide)
def f219 : ℕ := 0xfa4a6aa000bb1f70f000
def s500 : List ℕ := [f0,f2,f3,f1,f5,f219,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof491 : Ban 40 6 s500 := viaSmall (by decide +kernel) (by decide)
def f220 : ℕ := 0x4a0850e0a0000000e0f
def s501 : List ℕ := [f0,f220,f2,f3,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof492 : Ban 40 6 s501 := viaSmall (by decide +kernel) (by decide)
def f221 : ℕ := 0x8700f00000
def s502 : List ℕ := [f221,f0,f2,f3,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof493 : Ban 40 6 s502 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def f222 : ℕ := 0xff4afaaaa0fffffffff0
def s503 : List ℕ := [f0,f2,f3,f1,f5,f80,f222]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof494 : Ban 40 6 s503 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f223 : ℕ := 0xfa4a6aa00078ff0ff000
def s504 : List ℕ := [f0,f2,f3,f1,f5,f223,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof495 : Ban 40 6 s504 := viaSmall (by decide +kernel) (by decide)
def f224 : ℕ := 0x500900aa00000000ff0
def s505 : List ℕ := [f0,f2,f224,f3,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof496 : Ban 40 6 s505 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def f225 : ℕ := 0x1000488000309c4cc000
def s506 : List ℕ := [f0,f2,f3,f225,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof497 : Ban 40 6 s506 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def f226 : ℕ := 0xfade6ee54cfffffffdcc
def s507 : List ℕ := [f0,f2,f3,f1,f5,f80,f226]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof498 : Ban 40 6 s507 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f227 : ℕ := 0xea4a222000cf63b33000
def s508 : List ℕ := [f0,f2,f3,f1,f5,f227,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof499 : Ban 40 6 s508 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f228 : ℕ := 0x9404454c0000000dcc
def s509 : List ℕ := [f0,f228,f2,f3,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof500 : Ban 40 6 s509 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s510 : List ℕ := [f0,f2,f3,f81,f1,f80]
def rho23 : Projection 40 8 := pick [0,1,24,25,29,30,35,38] (by decide) (by decide) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof501 : Ban 40 6 s510 := viaCut rho23 w8 (by decide) (by decide +kernel) (by decide +kernel)
def s511 : List ℕ := [f0,f2,f3,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof502 : Ban 40 6 s511 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s512 : List ℕ := [f0,f2,f3,f81,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof503 : Ban 40 6 s512 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof440 : Ban 40 7 s446 := viaBranch (ws := [s447,s448,s449,s450,s451,s191,s452,s453,s454,s264,s316,s455,s372,s456,s457,s71,s458,s134,s459,s460,s461,s462,s463,s464,s465,s466,s467,s468,s469,s423,s426,s470,s472,s473,s474,s475,s476,s477,s478,s479,s480,s481,s482,s483,s484,s485,s486,s487,s488,s489,s490,s491,s492,s494,s496,s497,s498,s499,s500,s501,s502,s503,s504,s505,s506,s507,s508,s509,s510,s511,s512])
  (consBan proof441 (consBan proof442 (consBan proof443 (consBan proof444 (consBan proof445 (consBan proof183 (consBan proof446 (consBan proof447 (consBan proof448 (consBan proof255 (consBan proof306 (consBan proof449 (consBan proof365 (consBan proof450 (consBan proof451 (consBan proof65 (consBan proof452 (consBan proof128 (consBan proof453 (consBan proof454 (consBan proof455 (consBan proof456 (consBan proof457 (consBan proof458 (consBan proof459 (consBan proof460 (consBan proof461 (consBan proof462 (consBan proof463 (consBan proof416 (consBan proof418 (consBan proof464 (consBan proof465 (consBan proof466 (consBan proof467 (consBan proof468 (consBan proof469 (consBan proof470 (consBan proof471 (consBan proof472 (consBan proof473 (consBan proof474 (consBan proof475 (consBan proof476 (consBan proof477 (consBan proof478 (consBan proof479 (consBan proof480 (consBan proof481 (consBan proof482 (consBan proof483 (consBan proof484 (consBan proof485 (consBan proof486 (consBan proof487 (consBan proof488 (consBan proof489 (consBan proof490 (consBan proof491 (consBan proof492 (consBan proof493 (consBan proof494 (consBan proof495 (consBan proof496 (consBan proof497 (consBan proof498 (consBan proof499 (consBan proof500 (consBan proof501 (consBan proof502 (consBan proof503 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def s513 : List ℕ := [f0,f2,f3,f1,f5,f4,f80]
def s514 : List ℕ := [f0,f2,f3,f1,f46,f4,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof505 : Ban 40 6 s514 := viaSmall (by decide +kernel) (by decide)
def s515 : List ℕ := [f0,f2,f3,f1,f52,f4,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof506 : Ban 40 6 s515 := viaSmall (by decide +kernel) (by decide)
def s516 : List ℕ := [f0,f2,f3,f1,f53,f4,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof507 : Ban 40 6 s516 := viaSmall (by decide +kernel) (by decide)
def s517 : List ℕ := [f0,f2,f3,f1,f56,f4,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof508 : Ban 40 6 s517 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s518 : List ℕ := [f0,f2,f3,f1,f57,f4,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof509 : Ban 40 6 s518 := viaSmall (by decide +kernel) (by decide)
def s519 : List ℕ := [f154,f0,f2,f3,f1,f4,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof510 : Ban 40 6 s519 := viaCut rho12 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s520 : List ℕ := [f0,f2,f3,f157,f1,f4,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof511 : Ban 40 6 s520 := viaSmall (by decide +kernel) (by decide)
def s521 : List ℕ := [f63,f0,f2,f3,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof512 : Ban 40 6 s521 := viaSmall (by decide +kernel) (by decide)
def s522 : List ℕ := [f0,f2,f3,f1,f5,f64,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof513 : Ban 40 6 s522 := viaSmall (by decide +kernel) (by decide)
def s523 : List ℕ := [f0,f2,f3,f1,f5,f65,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof514 : Ban 40 6 s523 := viaSmall (by decide +kernel) (by decide)
def s524 : List ℕ := [f66,f0,f2,f3,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof515 : Ban 40 6 s524 := viaSmall (by decide +kernel) (by decide)
def s525 : List ℕ := [f67,f0,f2,f3,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof516 : Ban 40 6 s525 := viaSmall (by decide +kernel) (by decide)
def s526 : List ℕ := [f0,f2,f3,f1,f5,f80,f68]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof517 : Ban 40 6 s526 := viaSmall (by decide +kernel) (by decide)
def s527 : List ℕ := [f0,f2,f3,f1,f5,f69,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof518 : Ban 40 6 s527 := viaSmall (by decide +kernel) (by decide)
def s528 : List ℕ := [f0,f70,f2,f3,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof519 : Ban 40 6 s528 := viaSmall (by decide +kernel) (by decide)
def s529 : List ℕ := [f71,f0,f2,f3,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof520 : Ban 40 6 s529 := viaSmall (by decide +kernel) (by decide)
def s530 : List ℕ := [f0,f2,f3,f1,f5,f80,f72]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof521 : Ban 40 6 s530 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s531 : List ℕ := [f0,f2,f3,f1,f5,f73,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof522 : Ban 40 6 s531 := viaSmall (by decide +kernel) (by decide)
def s532 : List ℕ := [f0,f2,f74,f3,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof523 : Ban 40 6 s532 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s533 : List ℕ := [f0,f2,f3,f162,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof524 : Ban 40 6 s533 := viaSmall (by decide +kernel) (by decide)
def s534 : List ℕ := [f0,f2,f3,f1,f5,f163,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof525 : Ban 40 6 s534 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s535 : List ℕ := [f0,f2,f3,f1,f164,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof526 : Ban 40 6 s535 := viaSmall (by decide +kernel) (by decide)
def s536 : List ℕ := [f0,f165,f2,f3,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof527 : Ban 40 6 s536 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s537 : List ℕ := [f0,f2,f3,f1,f79,f80]
def rho24 : Projection 40 9 := pick [6,7,20,21,22,26,27,32,33] (by decide) (by decide) (by decide)
def f229 : ℕ := 0x6273
def f230 : ℕ := 0x10d9f
def f231 : ℕ := 0x2b1fc
def s538 : List ℕ := [f229,f230,f231]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w23 : Wide 9 3 s538 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof528 : Ban 40 6 s537 := viaCut rho24 w23 (by decide) (by decide +kernel) (by decide +kernel)
def s539 : List ℕ := [f0,f2,f3,f1,f79,f4,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof529 : Ban 40 6 s539 := viaSmall (by decide +kernel) (by decide)
def s540 : List ℕ := [f0,f2,f3,f1,f79,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof530 : Ban 40 6 s540 := viaSmall (by decide +kernel) (by decide)
def s541 : List ℕ := [f0,f2,f3,f81,f1,f4,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof531 : Ban 40 6 s541 := viaSmall (by decide +kernel) (by decide)
def s542 : List ℕ := [f0,f85,f2,f3,f1,f5,f80]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof532 : Ban 40 6 s542 := viaSmall (by decide +kernel) (by decide)
def s543 : List ℕ := [f208,f0,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof533 : Ban 40 6 s543 := viaCut rho1 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s544 : List ℕ := [f0,f2,f3,f1,f5,f4,f215]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof534 : Ban 40 6 s544 := viaSmall (by decide +kernel) (by decide)
def s545 : List ℕ := [f216,f0,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof535 : Ban 40 6 s545 := viaSmall (by decide +kernel) (by decide)
def s546 : List ℕ := [f217,f0,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof536 : Ban 40 6 s546 := viaCut rho9 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s547 : List ℕ := [f0,f2,f3,f1,f5,f4,f218]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof537 : Ban 40 6 s547 := viaSmall (by decide +kernel) (by decide)
def s548 : List ℕ := [f0,f2,f3,f1,f5,f4,f219]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof538 : Ban 40 6 s548 := viaSmall (by decide +kernel) (by decide)
def s549 : List ℕ := [f0,f220,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof539 : Ban 40 6 s549 := viaSmall (by decide +kernel) (by decide)
def s550 : List ℕ := [f221,f0,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof540 : Ban 40 6 s550 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s551 : List ℕ := [f0,f2,f3,f1,f5,f4,f222]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof541 : Ban 40 6 s551 := viaSmall (by decide +kernel) (by decide)
def s552 : List ℕ := [f0,f2,f3,f1,f5,f4,f223]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof542 : Ban 40 6 s552 := viaSmall (by decide +kernel) (by decide)
def s553 : List ℕ := [f0,f2,f224,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof543 : Ban 40 6 s553 := viaSmall (by decide +kernel) (by decide)
def s554 : List ℕ := [f0,f2,f3,f225,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof544 : Ban 40 6 s554 := viaSmall (by decide +kernel) (by decide)
def s555 : List ℕ := [f0,f2,f3,f1,f5,f4,f226]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof545 : Ban 40 6 s555 := viaSmall (by decide +kernel) (by decide)
def s556 : List ℕ := [f0,f2,f3,f1,f5,f227,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof546 : Ban 40 6 s556 := viaSmall (by decide +kernel) (by decide)
def s557 : List ℕ := [f0,f228,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof547 : Ban 40 6 s557 := viaSmall (by decide +kernel) (by decide)
def s558 : List ℕ := [f0,f2,f3,f81,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof548 : Ban 40 6 s558 := viaSmall (by decide +kernel) (by decide)
def s559 : List ℕ := [f0,f85,f2,f3,f1,f5,f4]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof549 : Ban 40 6 s559 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof504 : Ban 40 7 s513 := viaBranch (ws := [s265,s373,s72,s135,s425,s514,s515,s516,s517,s518,s519,s520,s521,s522,s523,s524,s525,s526,s527,s528,s529,s530,s531,s532,s533,s534,s535,s536,s537,s539,s540,s510,s541,s512,s542,s543,s430,s544,s545,s546,s547,s548,s549,s550,s551,s552,s553,s554,s555,s556,s557,s558,s559])
  (consBan proof256 (consBan proof366 (consBan proof66 (consBan proof129 (consBan proof417 (consBan proof505 (consBan proof506 (consBan proof507 (consBan proof508 (consBan proof509 (consBan proof510 (consBan proof511 (consBan proof512 (consBan proof513 (consBan proof514 (consBan proof515 (consBan proof516 (consBan proof517 (consBan proof518 (consBan proof519 (consBan proof520 (consBan proof521 (consBan proof522 (consBan proof523 (consBan proof524 (consBan proof525 (consBan proof526 (consBan proof527 (consBan proof528 (consBan proof529 (consBan proof530 (consBan proof501 (consBan proof531 (consBan proof503 (consBan proof532 (consBan proof533 (consBan proof422 (consBan proof534 (consBan proof535 (consBan proof536 (consBan proof537 (consBan proof538 (consBan proof539 (consBan proof540 (consBan proof541 (consBan proof542 (consBan proof543 (consBan proof544 (consBan proof545 (consBan proof546 (consBan proof547 (consBan proof548 (consBan proof549 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof550 : Ban 40 7 s559 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s560 : List ℕ := [f11,f0,f2,f3,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof552 : Ban 40 6 s560 := viaCut rho9 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s561 : List ℕ := [f0,f2,f12,f3,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof553 : Ban 40 6 s561 := viaSmall (by decide +kernel) (by decide)
def s562 : List ℕ := [f0,f13,f2,f3,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof554 : Ban 40 6 s562 := viaSmall (by decide +kernel) (by decide)
def s563 : List ℕ := [f14,f0,f2,f3,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof555 : Ban 40 6 s563 := viaSmall (by decide +kernel) (by decide)
def s564 : List ℕ := [f15,f0,f2,f3,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof556 : Ban 40 6 s564 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s565 : List ℕ := [f0,f2,f20,f3,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof557 : Ban 40 6 s565 := viaSmall (by decide +kernel) (by decide)
def s566 : List ℕ := [f21,f0,f2,f3,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof558 : Ban 40 6 s566 := viaSmall (by decide +kernel) (by decide)
def s567 : List ℕ := [f0,f25,f2,f3,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof559 : Ban 40 6 s567 := viaSmall (by decide +kernel) (by decide)
def s568 : List ℕ := [f0,f27,f2,f3,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof560 : Ban 40 6 s568 := viaSmall (by decide +kernel) (by decide)
def s569 : List ℕ := [f0,f28,f2,f3,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof561 : Ban 40 6 s569 := viaSmall (by decide +kernel) (by decide)
def f232 : ℕ := 0xf000
def s570 : List ℕ := [f232,f0,f2,f3,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w24 : Wide 8 2 s74 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof562 : Ban 40 6 s570 := viaCut rho23 w24 (by decide) (by decide +kernel) (by decide +kernel)
def f233 : ℕ := 0x10116af1150813fff33f
def s571 : List ℕ := [f0,f2,f3,f81,f233,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof563 : Ban 40 6 s571 := viaCut rho23 w8 (by decide) (by decide +kernel) (by decide +kernel)
def s572 : List ℕ := [f0,f2,f3,f203,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof564 : Ban 40 6 s572 := viaCut rho23 w24 (by decide) (by decide +kernel) (by decide +kernel)
def f234 : ℕ := 0x11005115081300033f
def s573 : List ℕ := [f234,f0,f2,f3,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof565 : Ban 40 6 s573 := viaSmall (by decide +kernel) (by decide)
def f235 : ℕ := 0x8f0000
def s574 : List ℕ := [f235,f0,f2,f3,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof566 : Ban 40 6 s574 := viaCut rho9 w1 (by decide) (by decide +kernel) (by decide +kernel)
def f236 : ℕ := 0x14a0efae0a44e0fffe0f
def s575 : List ℕ := [f0,f2,f3,f81,f1,f236,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof567 : Ban 40 6 s575 := viaSmall (by decide +kernel) (by decide)
def f237 : ℕ := 0x10006aa000000070f000
def s576 : List ℕ := [f0,f2,f3,f237,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof568 : Ban 40 6 s576 := viaCut rho9 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f238 : ℕ := 0x4a0850e0a44e0000e0f
def s577 : List ℕ := [f0,f238,f2,f3,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof569 : Ban 40 6 s577 := viaSmall (by decide +kernel) (by decide)
def f239 : ℕ := 0xf00000
def s578 : List ℕ := [f239,f0,f2,f3,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof570 : Ban 40 6 s578 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def f240 : ℕ := 0x1500faaaa08700fffff0
def s579 : List ℕ := [f0,f2,f3,f81,f1,f240,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof571 : Ban 40 6 s579 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f241 : ℕ := 0x10006aa00000000ff000
def s580 : List ℕ := [f0,f2,f3,f241,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof572 : Ban 40 6 s580 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def f242 : ℕ := 0x500900aa08700000ff0
def s581 : List ℕ := [f0,f2,f242,f3,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof573 : Ban 40 6 s581 := viaSmall (by decide +kernel) (by decide)
def s582 : List ℕ := [f6,f0,f2,f3,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof574 : Ban 40 6 s582 := viaSmall (by decide +kernel) (by decide)
def s583 : List ℕ := [f0,f2,f3,f81,f1,f10,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof575 : Ban 40 6 s583 := viaSmall (by decide +kernel) (by decide)
def s584 : List ℕ := [f0,f2,f3,f81,f32,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof576 : Ban 40 6 s584 := viaSmall (by decide +kernel) (by decide)
def s585 : List ℕ := [f104,f0,f2,f3,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof577 : Ban 40 6 s585 := viaSmall (by decide +kernel) (by decide)
def s586 : List ℕ := [f0,f105,f2,f3,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof578 : Ban 40 6 s586 := viaSmall (by decide +kernel) (by decide)
def s587 : List ℕ := [f0,f2,f3,f81,f1,f106,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof579 : Ban 40 6 s587 := viaSmall (by decide +kernel) (by decide)
def s588 : List ℕ := [f0,f2,f3,f81,f108,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof580 : Ban 40 6 s588 := viaSmall (by decide +kernel) (by decide)
def s589 : List ℕ := [f0,f107,f2,f3,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof581 : Ban 40 6 s589 := viaSmall (by decide +kernel) (by decide)
def s590 : List ℕ := [f131,f0,f2,f3,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof582 : Ban 40 6 s590 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s591 : List ℕ := [f0,f2,f3,f81,f1,f132,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof583 : Ban 40 6 s591 := viaSmall (by decide +kernel) (by decide)
def s592 : List ℕ := [f0,f2,f3,f81,f134,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof584 : Ban 40 6 s592 := viaSmall (by decide +kernel) (by decide)
def s593 : List ℕ := [f0,f2,f133,f3,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof585 : Ban 40 6 s593 := viaSmall (by decide +kernel) (by decide)
def f243 : ℕ := 0x100048800000004cc000
def s594 : List ℕ := [f0,f2,f3,f243,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof586 : Ban 40 6 s594 := viaSmall (by decide +kernel) (by decide)
def f244 : ℕ := 0x10946ee54c309cfffdcc
def s595 : List ℕ := [f0,f2,f3,f81,f244,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof587 : Ban 40 6 s595 := viaCut rho23 w8 (by decide) (by decide +kernel) (by decide +kernel)
def s596 : List ℕ := [f0,f2,f3,f81,f1,f244,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof588 : Ban 40 6 s596 := viaSmall (by decide +kernel) (by decide)
def f245 : ℕ := 0x9404454c309c000dcc
def s597 : List ℕ := [f0,f245,f2,f3,f81,f5]
def rho25 : Projection 40 8 := pick [0,1,12,13,15,16,17,19] (by decide) (by decide) (by decide)
def f246 : ℕ := 0x22e3
def f247 : ℕ := 0xd8fc
def s598 : List ℕ := [f22,f246,f247]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem w25 : Wide 8 3 s598 := viaSearch (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof589 : Ban 40 6 s597 := viaCut rho25 w25 (by decide) (by decide +kernel) (by decide +kernel)
def s599 : List ℕ := [f0,f245,f2,f3,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof590 : Ban 40 6 s599 := viaSmall (by decide +kernel) (by decide)
def f248 : ℕ := 0x2220000000b33000
def s600 : List ℕ := [f248,f0,f2,f3,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof591 : Ban 40 6 s600 := viaSmall (by decide +kernel) (by decide)
def s601 : List ℕ := [f44,f0,f2,f3,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof592 : Ban 40 6 s601 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s602 : List ℕ := [f0,f2,f3,f81,f1,f46,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof593 : Ban 40 6 s602 := viaSmall (by decide +kernel) (by decide)
def s603 : List ℕ := [f47,f0,f2,f3,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof594 : Ban 40 6 s603 := viaSmall (by decide +kernel) (by decide)
def s604 : List ℕ := [f51,f0,f2,f3,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof595 : Ban 40 6 s604 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s605 : List ℕ := [f0,f2,f3,f81,f1,f5,f52]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof596 : Ban 40 6 s605 := viaSmall (by decide +kernel) (by decide)
def s606 : List ℕ := [f0,f2,f3,f81,f1,f53,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof597 : Ban 40 6 s606 := viaSmall (by decide +kernel) (by decide)
def s607 : List ℕ := [f0,f54,f2,f3,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof598 : Ban 40 6 s607 := viaSmall (by decide +kernel) (by decide)
def s608 : List ℕ := [f55,f0,f2,f3,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof599 : Ban 40 6 s608 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s609 : List ℕ := [f0,f2,f3,f81,f1,f5,f56]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof600 : Ban 40 6 s609 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s610 : List ℕ := [f0,f2,f3,f81,f1,f57,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof601 : Ban 40 6 s610 := viaSmall (by decide +kernel) (by decide)
def s611 : List ℕ := [f0,f2,f58,f3,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof602 : Ban 40 6 s611 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof603 : Ban 40 6 s446 := viaCut rho0 w0 (by decide) (by decide +kernel) (by decide +kernel)
def s612 : List ℕ := [f154,f0,f2,f3,f81,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof604 : Ban 40 6 s612 := viaCut rho0 w1 (by decide) (by decide +kernel) (by decide +kernel)
def s613 : List ℕ := [f0,f2,f3,f81,f1,f5,f155]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof605 : Ban 40 6 s613 := viaSmall (by decide +kernel) (by decide)
def s614 : List ℕ := [f0,f2,f3,f81,f1,f156,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof606 : Ban 40 6 s614 := viaSmall (by decide +kernel) (by decide)
def s615 : List ℕ := [f0,f2,f3,f81,f157,f1,f5]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof607 : Ban 40 6 s615 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof551 : Ban 40 7 s511 := viaBranch (ws := [s560,s561,s562,s563,s564,s192,s565,s566,s567,s266,s317,s568,s374,s569,s570,s571,s572,s573,s574,s575,s576,s577,s578,s579,s580,s581,s582,s73,s583,s136,s584,s585,s586,s587,s588,s589,s590,s591,s592,s593,s594,s595,s596,s597,s599,s600,s601,s427,s602,s603,s604,s605,s606,s607,s608,s609,s610,s611,s446,s510,s512,s612,s613,s614,s615])
  (consBan proof552 (consBan proof553 (consBan proof554 (consBan proof555 (consBan proof556 (consBan proof184 (consBan proof557 (consBan proof558 (consBan proof559 (consBan proof257 (consBan proof307 (consBan proof560 (consBan proof367 (consBan proof561 (consBan proof562 (consBan proof563 (consBan proof564 (consBan proof565 (consBan proof566 (consBan proof567 (consBan proof568 (consBan proof569 (consBan proof570 (consBan proof571 (consBan proof572 (consBan proof573 (consBan proof574 (consBan proof67 (consBan proof575 (consBan proof130 (consBan proof576 (consBan proof577 (consBan proof578 (consBan proof579 (consBan proof580 (consBan proof581 (consBan proof582 (consBan proof583 (consBan proof584 (consBan proof585 (consBan proof586 (consBan proof587 (consBan proof588 (consBan proof589 (consBan proof590 (consBan proof591 (consBan proof592 (consBan proof419 (consBan proof593 (consBan proof594 (consBan proof595 (consBan proof596 (consBan proof597 (consBan proof598 (consBan proof599 (consBan proof600 (consBan proof601 (consBan proof602 (consBan proof603 (consBan proof501 (consBan proof503 (consBan proof604 (consBan proof605 (consBan proof606 (consBan proof607 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof608 : Ban 40 7 s558 := viaCut rho12 w0 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem proof0 : Ban 40 8 s0 := viaBranch (ws := [s1,s3,s77,s25,s139,s140,s141,s142,s143,s144,s145,s146,s147,s148,s149,s150,s163,s168,s193,s194,s195,s196,s197,s198,s269,s284,s211,s285,s377,s378,s379,s380,s381,s382,s383,s384,s385,s386,s387,s388,s389,s390,s391,s392,s393,s394,s410,s422,s433,s434,s435,s436,s437,s438,s439,s440,s441,s442,s443,s444,s445,s446,s513,s559,s511,s558])
  (consBan proof1 (consBan proof2 (consBan proof70 (consBan proof71 (consBan proof133 (consBan proof134 (consBan proof135 (consBan proof136 (consBan proof137 (consBan proof138 (consBan proof139 (consBan proof140 (consBan proof141 (consBan proof142 (consBan proof143 (consBan proof144 (consBan proof185 (consBan proof186 (consBan proof187 (consBan proof188 (consBan proof189 (consBan proof190 (consBan proof191 (consBan proof192 (consBan proof260 (consBan proof308 (consBan proof309 (consBan proof370 (consBan proof371 (consBan proof372 (consBan proof373 (consBan proof374 (consBan proof375 (consBan proof376 (consBan proof377 (consBan proof378 (consBan proof379 (consBan proof380 (consBan proof381 (consBan proof382 (consBan proof383 (consBan proof384 (consBan proof385 (consBan proof386 (consBan proof387 (consBan proof388 (consBan proof425 (consBan proof426 (consBan proof427 (consBan proof428 (consBan proof429 (consBan proof430 (consBan proof431 (consBan proof432 (consBan proof433 (consBan proof434 (consBan proof435 (consBan proof436 (consBan proof437 (consBan proof438 (consBan proof439 (consBan proof440 (consBan proof504 (consBan proof550 (consBan proof551 (consBan proof608 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
theorem cert6 : Ban 40 8 s0 := proof0
end PEqualNP.Outside.L_meta_11068

namespace PEqualNP.Outside.L_meta_11068
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def vSix : List ℕ := [0x11005115081300f33f,0x10944cc54c309c4ccdcc,0x4a0850e0a44e08f0e0f,0x500900aa08700f00ff0,0xf8006aa000f800fff000,0xea4a000000ffff000000]
def inputs : List ℕ := [0x2200a22a081300f33f,0x10000000000,0x2128998a98309c4ccdcc,0x9410a1c1444e08f0e0f,0x20a012015418700f00ff0,0x1f000d54000f800fff000,0x1d494000000ffff000000]
def core : Projection 41 40 := pick (List.range 40) (by decide) (by decide) (by decide)
set_option maxRecDepth 10000 in
theorem narrow (h : Ban 40 8 vSix) : Ban 41 9 inputs := viaCut core (widen (by decide +kernel) h) (by decide) (by decide +kernel) (by decide +kernel)
def posBits : ℕ := 0x12e1a3264c362850992244589120c170d183058b14284a950a13870c9528508911a34489
def negBits : ℕ := 0x10c183024c062010190040580120013091010483100848150013030c0520108011814401
def sample (bank : ℕ) (i : Fin 41) (j : Fin 7) := bank.testBit (7*i.val+j.val)

def seeds : List Wire := inputs.map (fun a => (false,a))
set_option maxHeartbeats 1000000 in
theorem listed : ∀ i : Fin 41, seeds.map (read i.val)=List.ofFn (sample posBits i) ∧
    seeds.map (read (41+i.val))=List.ofFn (sample negBits i) := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem labels : ∀ i : Fin 41, PEqualNP.Outside.L_meta_11068.Example.f (sample posBits i)=true ∧ PEqualNP.Outside.L_meta_11068.Example.f (sample negBits i)=false := by decide +kernel
theorem essential : ∀ a∈inputs, ∃ i : Fin 41, ∀ b∈inputs, b.testBit i.val≠b.testBit (41+i.val) → b=a := by decide +kernel
theorem initial {k S} (live : Live 41 k S) (sub : ∀ a∈S,a∈inputs) : S=inputs.toFinset := by
  apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
  intro a ha
  obtain ⟨i,h⟩ := essential a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
  exact h b (sub b hb) sep ▸ hb
theorem trace (C : Circuit) (fan : FanInTwo C) (eq : circuitFun 7 C=PEqualNP.Outside.L_meta_11068.Example.f) :
    ∃ k≤C.gates.countP counted, Live 41 k inputs.toFinset := by
  let final := execute C.gates seeds
  let out := final.getD C.output zero
  have ev (i : ℕ) : read i out = C.eval (seeds.map (read i)) := by
    rw [show read i out = (final.map (read i)).getD C.output false from (read_get i final C.output).symm]
    rw [show final=execute C.gates seeds from rfl,execute_read i _ _ fan];rfl
  have result (x : Fin 7 → Bool) : C.eval (List.ofFn x)=PEqualNP.Outside.L_meta_11068.Example.f x := congrFun eq x
  have good : Good 41 out.2 := by
    intro i hi same
    let j : Fin 41 := ⟨i,hi⟩
    have diff : read i out=read (41+i) out := by simp [read,same]
    have p := ev i;have n := ev (41+i)
    rw [(listed j).1,result,(labels j).1] at p
    rw [(listed j).2,result,(labels j).2] at n
    rw [p,n] at diff;contradiction
  have nz : out.2≠0 := by
    intro z;have bad := good 0 (by decide);simp [z] at bad
  have found : out.2∈ reps final := (get_simple final C.output).resolve_left nz
  obtain ⟨k,S,limit,live,sub⟩ := extract good nz C.gates seeds found
  have stays : ∀ a∈S, a∈inputs := by simpa [reps,seeds,List.map_map,Function.comp_def] using sub
  exact ⟨k,limit,initial live stays ▸ live⟩


theorem counted_lt {gs : List Gate} (h : ∃ g ∈ gs, g.op = .not) : gs.countP counted < gs.length := by
  apply Nat.lt_of_le_of_ne List.countP_le_length
  intro eq
  obtain ⟨g,hg,hop⟩ := h
  have bad := List.countP_eq_length.mp eq g hg
  simp [counted,hop] at bad

theorem finish (base : Ban 40 8 vSix) (gs : List Gate) (o : ℕ)
    (fan : ∀ g∈gs, (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2)
    (eq : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = PEqualNP.Outside.L_meta_11068.Example.f x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = PEqualNP.Outside.L_meta_11068.Example.f x := by
  by_cases has : ∃ g∈gs,g.op=.not
  · obtain ⟨k,lim,live⟩ := trace ⟨gs,o⟩ (fun g hg => ⟨by rcases (fan g hg).1 with a|a|a <;> simp [a],(fan g hg).2⟩) (funext eq)
    have low : 10 ≤ k := by
      by_contra! bad
      exact narrow base k (by omega) live
    have cost := counted_lt has
    change k≤gs.countP counted at lim
    exact PEqualNP.Outside.L_meta_11068.Example.sufficient gs (by omega)
  · refine ⟨gs,o,?_,le_rfl,eq⟩
    intro g hg
    rcases (fan g hg).1 with a|b|n
    · exact ⟨Or.inl a,(fan g hg).2⟩
    · exact ⟨Or.inr b,(fan g hg).2⟩
    · exact False.elim (has ⟨g,hg,n⟩)
end PEqualNP.Outside.L_meta_11068

theorem PEqualNP.Outside.L_meta_11068 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fan _ eq
  exact PEqualNP.Outside.L_meta_11068.finish PEqualNP.Outside.L_meta_11068.cert6 gates o fan eq
