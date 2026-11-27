import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

namespace PEqualNP.Outside.L_meta_6089

-- The proof method (live-wire tables, the cut count and the kernel check of merge
-- sequences) is adapted from open-goat/pequalnp-proofs pull request 11670 (L-meta-5572).
-- The eight gates were found by a SAT search; the check below runs them on the sixteen
-- promised inputs.

def witness : Circuit :=
  ⟨[⟨.or,[1,4]⟩,⟨.or,[5,6]⟩,⟨.and,[2,9]⟩,⟨.or,[3,7]⟩,
    ⟨.or,[9,11]⟩,⟨.or,[0,8]⟩,⟨.and,[12,13]⟩,⟨.or,[10,14]⟩],15⟩

theorem upper : RepSizeAtMost (fun u v : Fin 4 => (5870 : ℕ).testBit (4*u.val+v.val)) 8 := by
  refine ⟨witness,?_,by decide,by decide⟩
  simp [Monotone2,witness]

-- Number the sixteen promised inputs in row-major order. A live wire stands for
-- the bit mask of the inputs on which it is true.

def positives : List ℕ := [1,2,3,5,6,7,9,10,12]
def negatives : List ℕ := [0,4,8,11,13,14,15]

def anyBag (s : Multiset ℕ) (f : ℕ → Bool) : Bool :=
  Quot.liftOn s (fun l : List ℕ => l.any f) (fun _ _ p => p.any_eq)

theorem anyBag_true (s : Multiset ℕ) (f : ℕ→Bool) : anyBag s f=true ↔ ∃ x∈s, f x=true := by
  induction s using Quot.inductionOn with
  | _ l => exact List.any_eq_true

def separated (s : Multiset ℕ) : Bool := positives.all fun r =>
  negatives.all fun t => anyBag s fun w => w.testBit r && !(w.testBit t)

def possible : ℕ → Multiset ℕ → Bool
  | 0,s => separated s
  | k+1,s => separated s && anyBag s (fun a => anyBag (s.erase a) fun b =>
      decide (a≤b) && (let tail := (s.erase a).erase b
        possible k ((a &&& b) ::ₘ tail) || possible k ((a ||| b) ::ₘ tail)))

def inputTables : List ℕ := [15,240,3840,61440,4369,8738,17476,34952]
def start : Multiset ℕ := inputTables

theorem sepOf {s : Multiset ℕ} (h : ∀ r∈positives,∀ t∈negatives,
    ∃ w∈s, w.testBit r=true ∧ w.testBit t=false) : separated s=true := by
  simpa [separated,List.all_eq_true,anyBag_true] using h

theorem fromMerge {k a b : ℕ} {more : Multiset ℕ} (sep : separated (a ::ₘ b ::ₘ more)=true)
    (sub : possible k ((a &&& b) ::ₘ more)=true ∨ possible k ((a ||| b) ::ₘ more)=true) :
    possible (k+1) (a ::ₘ b ::ₘ more)=true := by
  have ordered {x y : ℕ} (xy : x≤y) (s : Multiset ℕ) (ok : separated (x ::ₘ y ::ₘ s)=true)
      (rec : possible k ((x &&& y) ::ₘ s)=true ∨ possible k ((x ||| y) ::ₘ s)=true) :
      possible (k+1) (x ::ₘ y ::ₘ s)=true := by
    simp only [possible,Bool.and_eq_true,anyBag_true,decide_eq_true_iff]
    refine ⟨ok,x,by simp,y,by simp,xy,?_⟩
    simpa using rec
  rcases le_total a b with ab|ba
  · exact ordered ab more sep sub
  · rw [Multiset.cons_swap a b] at sep ⊢
    exact ordered ba more sep (by simpa only [Nat.and_comm b a,Nat.or_comm b a] using sub)

-- Compute the input wires of each suffix by tracing back from the output.
-- Monotonicity requires those wires to distinguish every positive row from every negative row.

def full : ℕ := 65535
def gateTable (g : Gate) (w : ℕ → ℕ) : ℕ :=
  match g.inputs with
  | [] => match g.op with | .and => full | _ => 0
  | [a] => w a
  | a::b::_ => match g.op with | .and => w a &&& w b | _ => w a ||| w b

def trace (n : ℕ) (gs : List Gate) (w : ℕ → ℕ) (o : ℕ) : ℕ :=
  match gs with
  | [] => w o
  | g::tail => trace (n+1) tail (Function.update w n (gateTable g w)) o

def expand (T : Finset ℕ) (n : ℕ) (g : Gate) :=
  if n∈T then T.erase n ∪ g.inputs.toFinset else T

def cut (n : ℕ) (gs : List Gate) (o : ℕ) : Finset ℕ :=
  match gs with
  | [] => {o}
  | g::tail => expand (cut (n+1) tail o) n g

def legal (g : Gate) := (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2

theorem fullBit {r : ℕ} (h : r<16) : full.testBit r = true := by
  have all : ∀ i : Fin 16, full.testBit i.val=true := by decide
  exact all ⟨r,h⟩

theorem gateBit (g : Gate) (w : ℕ → ℕ) {r} (hr : r<16) (ok : legal g) :
    (gateTable g w).testBit r = g.op.eval (g.inputs.map fun i => (w i).testBit r) := by
  have ar := ok.2
  rcases inputs : g.inputs with _ | ⟨a,_|⟨b,more⟩⟩
  · rcases ok.1 with op|op <;> simp [gateTable,inputs,op,GateOp.eval,fullBit hr]
  · rcases ok.1 with op|op <;> simp [gateTable,inputs,op,GateOp.eval]
  · have empty : more=[] := by simpa [inputs] using ar
    subst more
    rcases ok.1 with op|op <;> simp [gateTable,inputs,op,GateOp.eval,Nat.testBit_and,Nat.testBit_or]

theorem gateOrder (g : Gate) (w : ℕ→ℕ) {r t} (hr : r<16) (ht : t<16) (ok : legal g)
    (mon : ∀ i∈g.inputs, (w i).testBit r=true → (w i).testBit t=true) :
    (gateTable g w).testBit r=true → (gateTable g w).testBit t=true := by
  rw [gateBit g w hr ok,gateBit g w ht ok]
  rcases ok.1 with op|op
  · simp only [op,GateOp.eval,List.all_map,Function.id_comp,List.all_eq_true]
    exact fun h i hi => mon i hi (h i hi)
  · simp only [op,GateOp.eval,List.any_map,Function.id_comp,List.any_eq_true]
    rintro ⟨i,hi,h⟩
    exact ⟨i,hi,mon i hi h⟩

theorem traceOrder (gs : List Gate) (hg : ∀ g∈gs, legal g) (n o : ℕ) (w : ℕ→ℕ)
    {r t} (hr : r<16) (ht : t<16)
    (mon : ∀ i∈cut n gs o, (w i).testBit r=true → (w i).testBit t=true) :
    (trace n gs w o).testBit r=true → (trace n gs w o).testBit t=true := by
  induction gs generalizing n w with
  | nil => exact mon o (by simp [cut])
  | cons g gs ih =>
    let T := cut (n+1) gs o
    apply ih (fun z hz => hg _ (List.mem_cons_of_mem _ hz)) (n+1) (Function.update w n (gateTable g w))
    intro i hi
    change i∈T at hi
    change ∀ i∈expand T n g, _ at mon
    by_cases eq : i=n
    · subst i
      simp only [Function.update_self]
      apply gateOrder g w hr ht (hg _ List.mem_cons_self)
      intro u hu
      exact mon u (by simp [expand,hi,hu])
    · rw [Function.update_of_ne eq]
      apply mon i
      by_cases live : n∈T
      · exact (by simp [expand,live,hi,eq])
      · simpa [expand,live] using hi

theorem cutBound (gs : List Gate) (hg : ∀ g∈gs, legal g) (n o : ℕ) : (cut n gs o).card ≤ gs.length+1 := by
  induction gs generalizing n with
  | nil => simp [cut]
  | cons g gs ih =>
    let T := cut (n+1) gs o
    have bound : T.card≤gs.length+1 := ih (fun z hz => hg _ (List.mem_cons_of_mem _ hz)) _
    change (expand T n g).card≤_
    have ar := (hg g List.mem_cons_self).2
    by_cases live : n∈T
    · have rem := Finset.card_erase_add_one live
      have cost := Finset.card_union_le (T.erase n) g.inputs.toFinset
      have args := g.inputs.toFinset_card_le
      simp only [expand,ite_eq_left live,List.length_cons]
      omega
    · simpa [expand,live] using bound.trans (Nat.le_succ _)

def separatedAt (n : ℕ) (gs : List Gate) (w : ℕ→ℕ) (o : ℕ) : Prop :=
  ∀ r∈positives,∀ t∈negatives,(trace n gs w o).testBit r=true ∧ (trace n gs w o).testBit t=false

theorem scanSep (gs : List Gate) (hg : ∀ g∈gs, legal g) (n o : ℕ) (w : ℕ→ℕ)
    (hits : separatedAt n gs w o) : separated ((cut n gs o).val.map w)=true := by
  apply sepOf
  intro r hr t ht
  have rp : r<16 := (by decide : ∀ z∈positives,z<16) r hr
  have tp : t<16 := (by decide : ∀ z∈negatives,z<16) t ht
  by_contra! no
  obtain ⟨pos,neg⟩ := hits r hr t ht
  have out := traceOrder gs hg n o w rp tp (fun i hi on => by
    have off := no (w i) (Multiset.mem_map_of_mem w hi) on
    simpa using off) pos
  simp_all

-- A binary gate can increase the number of live wires by at most one when traced
-- backwards. Equality forces it to replace two distinct wires that occur nowhere else
-- in the live set. Going forward, the gates are then a succession of disjoint pair merges.

theorem tightStep (T : Finset ℕ) (n k : ℕ) (g : Gate) (arity : g.inputs.length≤2)
    (upper : T.card≤k+1) (tight : (expand T n g).card=k+2) :
    ∃ a b, g.inputs=[a,b] ∧ a≠b ∧ n∈T ∧ a∉T.erase n ∧ b∉T.erase n ∧ T.card=k+1 ∧
      expand T n g = insert a (insert b (T.erase n)) := by
  have live : n∈T := by
    by_contra miss
    simp [expand,miss] at tight
    omega
  let R := T.erase n
  have rem : R.card+1=T.card := Finset.card_erase_add_one live
  have use := Finset.card_union_le R g.inputs.toFinset
  have count := g.inputs.toFinset_card_le
  have eq : (R ∪ g.inputs.toFinset).card=k+2 := by simpa [expand,live,R] using tight
  have len : g.inputs.length=2 := by omega
  obtain ⟨a,b,ab⟩ := List.length_eq_two.mp len
  have form : expand T n g = insert a (insert b R) := by
    ext v
    simp [expand,live,ab,R]
  have high : R.card+1 < (insert a (insert b R)).card := by rw [← form,tight];omega
  have ai : a ∉ insert b R := by
    intro yes
    rw [Finset.insert_eq_of_mem yes] at high
    exact (Nat.not_lt_of_ge (Finset.card_insert_le b R)) high
  have bi : b ∉ R := by
    intro yes
    rw [Finset.insert_eq_of_mem yes] at high
    exact (Nat.not_lt_of_ge (Finset.card_insert_le a R)) high
  have ane : a≠b := fun e => ai (by simp [e])
  exact ⟨a,b,ab,ane,live,fun h => ai (Finset.mem_insert_of_mem h),bi,by omega,form⟩

theorem follows (gs : List Gate) (hg : ∀ g∈gs, legal g) (n o : ℕ) (w : ℕ→ℕ)
    (tight : (cut n gs o).card=gs.length+1) (hits : separatedAt n gs w o) :
    possible gs.length ((cut n gs o).val.map w)=true := by
  have sep := scanSep gs hg n o w hits
  induction gs generalizing n w with
  | nil => exact sep
  | cons g gs ih =>
    let T := cut (n+1) gs o
    let R := T.erase n
    let v := gateTable g w
    let w' := Function.update w n v
    have ok := hg g List.mem_cons_self
    have rest : ∀ z∈gs,legal z := fun z hz => hg _ (List.mem_cons_of_mem _ hz)
    obtain ⟨a,b,ab,ne,live,ha,hb,bound,eq⟩ := tightStep T n gs.length g ok.2 (cutBound gs rest _ o) tight
    have src : ((cut n (g::gs) o).val.map w) = w a ::ₘ w b ::ₘ R.val.map w := by
      change (expand T n g).val.map w = _
      rw [eq,Finset.insert_val_of_notMem (by simp [ne,ha]), Finset.insert_val_of_notMem hb]
      simp [R]
    have tgt : T.val.map w' = v ::ₘ R.val.map w := by
      have teq : T=insert n R := (Finset.insert_erase live).symm
      calc
        _ = (insert n R).val.map w' := congrArg (fun S : Finset ℕ => S.val.map w') teq
        _ = v ::ₘ R.val.map w' := by rw [Finset.insert_val_of_notMem (by simp [R]),Multiset.map_cons];simp [w']
        _ = _ := by
          apply congrArg (Multiset.cons v)
          apply Multiset.map_congr rfl
          intro i hi
          exact Function.update_of_ne (Finset.mem_erase.mp hi).1 v w
    have hh : separatedAt (n+1) gs w' o := hits
    have sub := ih rest (n+1) w' bound hh (scanSep gs rest _ _ _ hh)
    change possible gs.length (T.val.map w')=true at sub
    rw [tgt] at sub
    rw [src] at sep ⊢
    apply fromMerge sep
    rcases ok.1 with op|op
    · left
      have same : v=w a &&& w b := by
        change gateTable g w=_
        simp [gateTable,op,ab]
      simpa [same] using sub
    · right
      have same : v=w a ||| w b := by simp [v,gateTable,op,ab]
      simpa [same] using sub

-- The kernel checks every feasible succession of seven merges.

set_option maxRecDepth 80000 in
theorem noMerges : possible 7 start=false := by decide +kernel

-- Each of the eight initial wires is indispensable. Seven gates would therefore
-- attain equality at every cut and produce one of the merge sequences checked above.

def raw (i : ℕ) := inputTables.getD i 0

theorem traceEval (gs : List Gate) (ok : ∀ g∈gs,legal g) (o r : ℕ) (hr : r<16)
    (l : List Bool) (w : ℕ→ℕ) (agree : ∀ i,(w i).testBit r=l.getD i false) :
    (trace l.length gs w o).testBit r =
    (gs.foldl (fun s g => s++[g.op.eval (g.inputs.map fun i => s.getD i false)]) l).getD o false := by
  induction gs generalizing l w with
  | nil => exact agree o
  | cons g gs ih =>
    let value := g.op.eval (g.inputs.map fun i => l.getD i false)
    let l' := l++[value]
    have hlen : l'.length=l.length+1 := by simp [l']
    have bit : (gateTable g w).testBit r=value := by rw [gateBit g w hr (ok _ List.mem_cons_self)]; simp only [agree,value]
    change (trace (l.length+1) gs _ o).testBit r = (List.foldl _ l' gs).getD o false
    rw [← hlen]
    apply ih (fun t ht => ok _ (List.mem_cons_of_mem _ ht))
    intro i
    by_cases eq : i=l.length
    · subst i
      simpa [l',List.getD_eq_getElem?_getD] using bit
    · rw [Function.update_of_ne eq,agree]
      by_cases low : i<l.length
      · exact (List.getD_append _ _ _ _ low).symm
      · rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)]

theorem initial (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 4 => (5870 : ℕ).testBit (4*u.val+v.val)) C) :
    separatedAt 8 C.gates raw C.output := by
  have legalAll : ∀ g∈C.gates,legal g := by
    intro g hg
    exact ⟨by simpa using (hm g hg).1,(hm g hg).2⟩
  have finiteEq : ∀ u v : Fin 4,∀ j : Fin 8, (raw j.val).testBit (4*u.val+v.val)=(oneEach u v).getD j.val false := by decide
  have atRow (u v : Fin 4) :
      (trace 8 C.gates raw C.output).testBit (4*u.val+v.val)=(5870 : ℕ).testBit (4*u.val+v.val) := by
    have len : (oneEach u v).length=8 := by simp [oneEach]
    have h := traceEval C.gates legalAll C.output (4*u.val+v.val) (by omega) (oneEach u v) raw (fun j => by
      by_cases inside : j<8
      · exact finiteEq u v ⟨j,inside⟩
      · have nil : raw j=0 := List.getD_eq_default _ _ (by change 8≤j;omega)
        rw [List.getD_eq_default _ _ (by omega : (oneEach u v).length≤j),nil]
        simp)
    rw [len] at h
    exact h.trans (rep u v)
  intro r hr t ht
  have allP : ∀ k∈positives,∃ u v : Fin 4, k=4*u.val+v.val ∧ (5870 : ℕ).testBit k=true := by decide
  have allN : ∀ k∈negatives,∃ u v : Fin 4, k=4*u.val+v.val ∧ (5870 : ℕ).testBit k=false := by decide
  obtain ⟨u,v,rfl,pos⟩ := allP r hr
  obtain ⟨a,b,rfl,neg⟩ := allN t ht
  exact ⟨(atRow u v).trans pos,(atRow a b).trans neg⟩

theorem lower : ¬RepSizeAtMost (fun u v : Fin 4 => (5870 : ℕ).testBit (4*u.val+v.val)) 7 := by
  rintro ⟨C,hm,small,rep⟩
  have good : ∀ g∈C.gates,legal g := by
    intro g hg
    exact ⟨by simpa using (hm g hg).1,(hm g hg).2⟩
  have hits := initial C hm rep
  let S := cut 8 C.gates C.output
  have needed : ∀ i : Fin 8, ∃ r∈positives,∃ t∈negatives,∀ j : Fin 8,j≠i →
      (raw j.val).testBit r=true → (raw j.val).testBit t=true := by decide
  have all : Finset.range 8 ⊆ S := by
    intro i hi
    let j : Fin 8 := ⟨i,Finset.mem_range.mp hi⟩
    by_contra miss
    obtain ⟨r,hr,t,ht,mon⟩ := needed j
    obtain ⟨pos,neg⟩ := hits r hr t ht
    have rp := (by decide : ∀ k∈positives,k<16) r hr
    have tp := (by decide : ∀ k∈negatives,k<16) t ht
    have bad := traceOrder C.gates good 8 C.output raw rp tp (fun k hk => by
      by_cases inside : k<8
      · apply mon ⟨k,inside⟩
        intro eq
        have equal : k=i := congrArg Fin.val eq
        exact miss (equal ▸ hk)
      · have nil : raw k=0 := List.getD_eq_default _ _ (by change 8≤k;omega)
        simp [nil]) pos
    simp_all
  have price : 8≤S.card := by simpa using Finset.card_le_card all
  have limit : S.card≤C.gates.length+1 := cutBound _ good _ _
  change C.gates.length≤7 at small
  have sz : C.gates.length=7 := by omega
  have eq : Finset.range 8=S := Finset.eq_of_subset_of_card_le all (by simp;omega)
  have ok := follows C.gates good 8 C.output raw (by change S.card=_;omega) hits
  change possible C.gates.length (S.val.map raw)=true at ok
  rw [sz,←eq] at ok
  have masks : (Finset.range 8).val.map raw=start := by decide
  rw [masks,noMerges] at ok
  contradiction

end PEqualNP.Outside.L_meta_6089

theorem PEqualNP.Outside.L_meta_6089 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (5870 : ℕ).testBit (4 * u.val + v.val)) 8 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (5870 : ℕ).testBit (4 * u.val + v.val)) 7 :=
  ⟨PEqualNP.Outside.L_meta_6089.upper, PEqualNP.Outside.L_meta_6089.lower⟩
