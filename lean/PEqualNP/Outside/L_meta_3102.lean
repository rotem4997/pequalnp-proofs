import Mathlib.Data.List.OfFn
import Mathlib.Tactic.IntervalCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3102

-- The staged construction adapts the checked proof of L-meta-2189.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def collapseIndex (i : Nat) : Nat :=
  if i < 8 then i else if i = 8 then 1 else i - 1

def collapseGate (g : Gate) : Gate := ⟨g.op, g.inputs.map collapseIndex⟩

def collapseCircuit (C : Circuit) : Circuit :=
  ⟨C.gates.map collapseGate, collapseIndex C.output⟩

theorem collapse_read (x : Fin 8 → Bool) (extra : List Bool) (i : Nat) :
    (List.ofFn x ++ extra).getD (collapseIndex i) false =
    ((List.ofFn x ++ [x 1]) ++ extra).getD i false := by
  by_cases low : i < 8
  · simp only [collapseIndex, if_pos low]
    rw [List.getD_append _ _ _ _ (by simpa using low),
      List.getD_append _ _ _ _ (by simp; omega),
      List.getD_append _ _ _ _ (by simpa using low)]
  by_cases equal : i = 8
  · subst i
    simp only [collapseIndex, lt_self_iff_false, if_false, if_true]
    rw [List.getD_append _ _ _ _ (by simp),
      List.getD_append _ _ _ _ (by simp),
      List.getD_append_right _ _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD]
  · rw [List.getD_append_right _ _ _ _ (by simp [collapseIndex, low, equal]; omega),
      List.getD_append_right _ _ _ _ (by simp; omega)]
    congr 1
    simp [collapseIndex, low, equal]
    omega

def collapseStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

theorem collapse_fold (gs : List Gate) (x : Fin 8 → Bool) (extra : List Bool) :
    ∃ tail : List Bool,
    (gs.map collapseGate).foldl collapseStep (List.ofFn x ++ extra) = List.ofFn x ++ tail ∧
    gs.foldl collapseStep ((List.ofFn x ++ [x 1]) ++ extra) = (List.ofFn x ++ [x 1]) ++ tail := by
  induction gs generalizing extra with
  | nil => exact ⟨extra, rfl, rfl⟩
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map fun i => ((List.ofFn x ++ [x 1]) ++ extra).getD i false)
    obtain ⟨tail, h8, h9⟩ := ih (extra ++ [v])
    refine ⟨tail, ?_, ?_⟩
    · simp only [List.map_cons, List.foldl_cons, collapseStep, collapseGate, List.map_map,
        Function.comp_def, collapse_read, List.append_assoc]
      exact h8
    · simp only [List.foldl_cons, collapseStep, List.append_assoc] at h9 ⊢
      exact h9

theorem collapsed_wires (gs : List Gate) (x : Fin 8 → Bool) (i : Nat) :
    ((⟨gs.map collapseGate, 0⟩ : Circuit).wires (List.ofFn x)).getD (collapseIndex i) false =
    ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x ++ [x 1])).getD i false := by
  obtain ⟨t, h8, h9⟩ := collapse_fold gs x []
  simp only [List.append_nil] at h8 h9
  change ((gs.map collapseGate).foldl collapseStep _).getD _ _ = (gs.foldl collapseStep _).getD _ _
  rw [h8, h9]
  exact collapse_read x t i

theorem collapsed_eval (C : Circuit) (x : Fin 8 → Bool) :
    (collapseCircuit C).eval (List.ofFn x) = C.eval (List.ofFn x ++ [x 1]) :=
  collapsed_wires C.gates x C.output

theorem collapsed_fan {C : Circuit} (fan : FanInTwo C) : FanInTwo (collapseCircuit C) := by
  intro g hg
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
  simpa [collapseGate] using fan p hp

theorem collapsed_size (C : Circuit) : (collapseCircuit C).size = C.size := by
  simp [collapseCircuit, Circuit.size]

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev X := Fin 8 → Bool
abbrev F := X → Bool → Bool
abbrev Bank := X → Bool → List Bool
abbrev Pool := F → Prop

def gateOK (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
def good (gs : List Gate) := ∀ g ∈ gs, gateOK g
def plus (s : Pool) (f : F) : Pool := fun h => s h ∨ h = f
def readB (w : Bank) (i : ℕ) : F := fun x b => (w x b).getD i false
def real (n : ℕ) (w : Bank) (f : F) := ∃ i < n, readB w i = f
def pureB (f : F) := ∃ c : Bool → Bool, (c false = true → c true = true) ∧ ∀ x b, f x b = c b
def low (f : F) : F := fun x _ => f x false
def lowConst (f : F) := ∃ c : Bool, ∀ x, f x false = c
def base (p : List Gate) : Bank := fun x b => (Circuit.mk p 0).wires (List.ofFn x ++ [x 1 || b])
def fixed (p : List Gate) : Bank := fun x _ => base p x false
def joint (p : List Gate) (i : ℕ) (d : Bool) (t : List Gate) : Bank := fun x b =>
  let w := base p x b
  (Circuit.mk t 0).wires (w ++ [if b then true else w.getD i false])
def sz (p : List Gate) := 9 + p.length
def jsz (p t : List Gate) := sz p + 1 + t.length

def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def run (gs : List Gate) (w : List Bool) := gs.foldl step w
theorem run_ext (gs : List Gate) (w : List Bool) :
    ∃ e, run gs w = w ++ e ∧ e.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[],by simp [run],rfl⟩
  | cons g gs ih =>
    obtain ⟨e,he,hl⟩ := ih (step w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: e,?_,by simpa using hl⟩
    change run gs (step w g) = _
    rw [he]
    simp [step,List.append_assoc]
theorem run_len (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  obtain ⟨e,he,hl⟩ := run_ext gs w
  simp [he,hl]
theorem base_len (p : List Gate) (x : X) (b : Bool) : (base p x b).length = sz p := by
  change (run p _).length = _
  simp [run_len,sz]
theorem fixed_len (p : List Gate) (x : X) (b : Bool) : (fixed p x b).length = sz p :=
  base_len p x false

theorem joint_len (p t : List Gate) (i : ℕ) (d : Bool) (x : X) (b : Bool) :
    (joint p i d t x b).length = jsz p t := by
  change (run t _).length = _
  simp [run_len,base_len,jsz]
theorem snocGood {p : List Gate} {g : Gate} (h : good p) (hg : gateOK g) : good (p ++ [g]) := by
  intro a ha
  rcases List.mem_append.mp ha with hp | hs
  · exact h _ hp
  · simpa only [List.mem_singleton.mp hs] using hg

def extend (w : Bank) (g : Gate) : Bank := fun x b => step (w x b) g
theorem base_snoc (p : List Gate) (g : Gate) : base (p ++ [g]) = extend (base p) g := by
  funext x b
  simp [base,Circuit.wires,List.foldl_append,extend,step]
theorem fixed_snoc (p : List Gate) (g : Gate) : fixed (p ++ [g]) = extend (fixed p) g := by
  funext x b
  exact congrFun (congrFun (base_snoc p g) x) false

theorem joint_snoc (p t : List Gate) (i : ℕ) (d : Bool) (g : Gate) :
    joint p i d (t ++ [g]) = extend (joint p i d t) g := by
  funext x b
  simp [joint,Circuit.wires,List.foldl_append,extend,step]
theorem real_keep {n : ℕ} {w : Bank} {f : F} (len : ∀ x b, (w x b).length = n)
    (g : Gate) (h : real n w f) : real (n+1) (extend w g) f := by
  obtain ⟨i,hi,rfl⟩ := h
  refine ⟨i,by omega,?_⟩
  funext x b
  exact List.getD_append _ _ _ _ (by simpa only [len] using hi)

def builds (n : ℕ) (w : Bank) (f : F) := ∃ g, gateOK g ∧ readB (extend w g) n = f
def neg (a : F) : F := fun x b => !(a x b)
def op (d a b : Bool) := if d then a || b else a && b
def binary (d : Bool) (a b : F) : F := fun x k => op d (a x k) (b x k)
theorem op_comm (d a b : Bool) : op d a b = op d b a := by cases d <;> cases a <;> cases b <;> rfl
theorem bin_comm (d : Bool) (a b : F) : binary d a b = binary d b a := by
  funext x k; exact op_comm _ _ _
theorem op_hot (d a : Bool) : op d d a = d := by cases d <;> rfl
theorem op_cold (d a : Bool) : op d (!d) a = a := by cases d <;> rfl
theorem lastRead {n : ℕ} {w : Bank} (len : ∀ x b, (w x b).length = n) (g : Gate) (x : X) (b : Bool) :
    readB (extend w g) n x b = g.op.eval (g.inputs.map fun i => readB w i x b) := by
  simp only [readB,extend,step]
  rw [List.getD_append_right _ _ _ _ (by simp [len])]
  simp [len]
theorem builds_neg {n : ℕ} {w : Bank} {a : F} (len : ∀ x b, (w x b).length = n)
    (h : real n w a) : builds n w (neg a) := by
  obtain ⟨i,_,rfl⟩ := h
  refine ⟨⟨.not,[i]⟩,by simp [gateOK],?_⟩
  funext x b
  rw [lastRead len]
  rfl
theorem builds_bin {n : ℕ} {w : Bank} {a b : F} (len : ∀ x b, (w x b).length = n)
    (d : Bool) (ha : real n w a) (hb : real n w b) : builds n w (binary d a b) := by
  obtain ⟨i,_,rfl⟩ := ha
  obtain ⟨j,_,rfl⟩ := hb
  cases d
  · refine ⟨⟨.and,[i,j]⟩,by simp [gateOK],?_⟩
    funext x k
    rw [lastRead len]
    simp [GateOp.eval,binary,op]
  · refine ⟨⟨.or,[i,j]⟩,by simp [gateOK],?_⟩
    funext x k
    rw [lastRead len]
    simp [GateOp.eval,binary,op]

def ahead (p : List Gate) (f : F) := pureB f ∨ real (sz p) (base p) f
def behind (p t l : List Gate) (i : ℕ) (d : Bool) (f : F) :=
  lowConst f ∨ (real (jsz p t) (joint p i d t) f ∧ real (sz l) (fixed l) (low f))
def restricted (l : List Gate) (f : F) := lowConst f ∨ real (sz l) (fixed l) (low f)

def Stage (k : ℕ) (s : Pool) : Prop :=
  (∃ p, good p ∧ p.length ≤ k ∧ ∀ f, s f → ahead p f) ∨
  (∃ p t l i d, i < sz p ∧ good p ∧ good t ∧ good l ∧
    p.length+t.length+1 ≤ k ∧ l.length+1 ≤ k ∧ ∀ f, s f → behind p t l i d f) ∨
  (∃ l, good l ∧ l.length+2 ≤ k ∧ ∀ f, s f → restricted l f)

theorem Stage.before {k : ℕ} {s : Pool} (p : List Gate) (hp : good p)
    (bud : p.length ≤ k) (all : ∀ f, s f → ahead p f) : Stage k s :=
  Or.inl ⟨p,hp,bud,all⟩
theorem Stage.afterSwitch {k : ℕ} {s : Pool} (p t l : List Gate) (i : ℕ) (d : Bool)
    (hi : i < sz p) (hp : good p) (ht : good t) (hl : good l)
    (bud : p.length+t.length+1 ≤ k) (lb : l.length+1 ≤ k)
    (all : ∀ f, s f → behind p t l i d f) : Stage k s :=
  Or.inr (Or.inl ⟨p,t,l,i,d,hi,hp,ht,hl,bud,lb,all⟩)
theorem Stage.cheap {k : ℕ} {s : Pool} (l : List Gate) (hl : good l) (bud : l.length+2 ≤ k)
    (all : ∀ f, s f → restricted l f) : Stage k s :=
  Or.inr (Or.inr ⟨l,hl,bud,all⟩)

theorem includeMore {s : Pool} {a : F} {P : F → Prop}
    (old : ∀ f, s f → P f) (new : P a) : ∀ f, plus s a f → P f := by
  intro f h
  rcases h with h | rfl
  · exact old f h
  · exact new
theorem keepBase {p : List Gate} {f : F} (g : Gate) (h : real (sz p) (base p) f) :
    real (sz (p ++ [g])) (base (p ++ [g])) f := by
  rw [base_snoc]
  simpa [sz,Nat.add_assoc] using real_keep (base_len p) g h
theorem keepFixed {p : List Gate} {f : F} (g : Gate) (h : real (sz p) (fixed p) f) :
    real (sz (p ++ [g])) (fixed (p ++ [g])) f := by
  rw [fixed_snoc]
  simpa [sz,Nat.add_assoc] using real_keep (fixed_len p) g h

theorem keepJoint {p t : List Gate} {i : ℕ} {d : Bool} {f : F} (g : Gate)
    (h : real (jsz p t) (joint p i d t) f) :
    real (jsz p (t ++ [g])) (joint p i d (t ++ [g])) f := by
  rw [joint_snoc]
  simpa [jsz,Nat.add_assoc] using real_keep (joint_len p t i d) g h
theorem lastBase {p : List Gate} {g : Gate} {f : F} (h : readB (extend (base p) g) (sz p) = f) :
    real (sz (p ++ [g])) (base (p ++ [g])) f := by
  refine ⟨sz p,by simp [sz],by rwa [base_snoc]⟩
theorem lastFixed {p : List Gate} {g : Gate} {f : F} (h : readB (extend (fixed p) g) (sz p) = f) :
    real (sz (p ++ [g])) (fixed (p ++ [g])) f := by
  refine ⟨sz p,by simp [sz],by rwa [fixed_snoc]⟩

theorem lastJoint {p t : List Gate} {i : ℕ} {d : Bool} {g : Gate} {f : F}
    (h : readB (extend (joint p i d t) g) (jsz p t) = f) :
    real (jsz p (t ++ [g])) (joint p i d (t ++ [g])) f := by
  refine ⟨jsz p t,by simp [jsz],by rwa [joint_snoc]⟩


theorem pure_low {f : F} (h : pureB f) : lowConst f := by
  obtain ⟨c,_,hc⟩ := h
  exact ⟨c false,fun x => hc x false⟩
theorem base_low {p : List Gate} {a : F} (h : real (sz p) (base p) a) :
    real (sz p) (fixed p) (low a) := by
  obtain ⟨i,hi,rfl⟩ := h
  exact ⟨i,hi,rfl⟩
theorem liftJoint {p : List Gate} {f : F} (i : ℕ) (d : Bool) (h : real (sz p) (base p) f) :
    real (jsz p []) (joint p i d []) f := by
  obtain ⟨j,hj,rfl⟩ := h
  refine ⟨j,by simp [jsz]; omega,?_⟩
  funext x b
  exact List.getD_append _ _ _ _ (by simpa only [base_len] using hj)
theorem switchWire (p : List Gate) (i : ℕ) (d : Bool) :
    real (jsz p []) (joint p i d [])
      (fun x b => if b then true else readB (base p) i x b) := by
  refine ⟨sz p,by simp [jsz],?_⟩
  funext x b
  change (base p x b ++ [_]).getD (sz p) false = _
  rw [List.getD_append_right _ _ _ _ (by simp [base_len])]
  simp [base_len,readB]

theorem beforeNext {k : ℕ} {s : Pool} {f : F} {p : List Gate}
    (hp : good p) (bud : p.length ≤ k) (all : ∀ a, s a → ahead p a)
    (how : ahead p f ∨ builds (sz p) (base p) f) : Stage (k+1) (plus s f) := by
  rcases how with h | ⟨g,hg,he⟩
  · exact .before p hp (by omega) (includeMore all h)
  · refine .before (p++[g]) (snocGood hp hg) (by simp; omega) (includeMore ?_ (Or.inr (lastBase he)))
    intro a ha
    exact (all a ha).imp id (keepBase g)

theorem afterBuild {k : ℕ} {s : Pool} {f : F} {p t l : List Gate} {i : ℕ} {d : Bool}
    (hi : i < sz p) (hp : good p) (ht : good t) (hl : good l)
    (bud : p.length + t.length + 1 ≤ k) (lb : l.length + 1 ≤ k)
    (all : ∀ a, s a → behind p t l i d a)
    (jb : builds (jsz p t) (joint p i d t) f) (cb : builds (sz l) (fixed l) (low f)) :
    Stage (k+1) (plus s f) := by
  obtain ⟨g,hg,he⟩ := jb
  obtain ⟨q,hq,he'⟩ := cb
  refine .afterSwitch p (t++[g]) (l++[q]) i d hi hp (snocGood ht hg) (snocGood hl hq)
    (by simp; omega) (by simp; omega)
    (includeMore ?_ (Or.inr ⟨lastJoint he,lastFixed he'⟩))
  intro a ha
  rcases all a ha with c | ⟨r,r'⟩
  · exact Or.inl c
  · exact Or.inr ⟨keepJoint g r,keepFixed q r'⟩

theorem afterDrop {k : ℕ} {s : Pool} {f : F} {p t l : List Gate} {i : ℕ} {d : Bool}
    (hl : good l) (lb : l.length+1 ≤ k) (all : ∀ a, s a → behind p t l i d a)
    (h : restricted l f) : Stage (k+1) (plus s f) := by
  refine .cheap l hl (by omega) (includeMore ?_ h)
  intro a ha
  exact (all a ha).imp id And.right

theorem cheapNext {k : ℕ} {s : Pool} {f : F} {l : List Gate}
    (hl : good l) (lb : l.length + 2 ≤ k) (all : ∀ a, s a → restricted l a)
    (how : restricted l f ∨ builds (sz l) (fixed l) (low f)) : Stage (k+1) (plus s f) := by
  rcases how with h | ⟨g,hg,he⟩
  · exact .cheap l hl (by omega) (includeMore all h)
  · refine .cheap (l++[g]) (snocGood hl hg) (by simp; omega) (includeMore ?_ (Or.inr (lastFixed he)))
    intro a ha
    exact (all a ha).imp id (keepFixed g)

theorem beginSwitch {k : ℕ} {s : Pool} {f : F} {p : List Gate} (i : ℕ) (d : Bool)
    (hi : i < sz p) (hp : good p) (bud : p.length ≤ k) (all : ∀ a, s a → ahead p a)
    (new : behind p [] p i d f) : Stage (k+1) (plus s f) := by
  refine .afterSwitch p [] p i d hi hp (by intro q h; cases h) hp (by simp; omega) (by omega)
    (includeMore ?_ new)
  intro a ha
  rcases all a ha with h | h
  · exact Or.inl (pure_low h)
  · exact Or.inr ⟨liftJoint i d h,base_low h⟩

theorem mix {k : ℕ} {s : Pool} {p : List Gate} {a b : F} (d : Bool)
    (hp : good p) (bud : p.length ≤ k) (all : ∀ f, s f → ahead p f)
    (pa : pureB a) (rb : real (sz p) (base p) b) : Stage (k+1) (plus s (binary d a b)) := by
  obtain ⟨c,mono,hc⟩ := pa
  by_cases hot : c false = d
  · apply beginSwitch 0 false (by simp [sz]) hp bud all
    exact Or.inl ⟨d,fun x => by simp [binary,hc,hot,op_hot]⟩
  · have cold : c false = !d := by cases e : c false <;> cases d <;> simp_all
    by_cases hotHigh : c true = d
    · have hd : d = true := by cases d <;> simp_all
      rw [hd] at hotHigh cold ⊢
      obtain ⟨i,hi,rfl⟩ := rb
      apply beginSwitch i true hi hp bud all
      right
      constructor
      · have same : binary true a (readB (base p) i) =
            (fun x b => if b then true else readB (base p) i x b) := by
          funext x b
          cases b <;> simp [binary,hc,cold,hotHigh,op_cold,op_hot,op]
        rw [same]
        exact switchWire p i true
      · refine ⟨i,hi,?_⟩
        funext x b
        simp [low,binary,hc,cold,op_cold,readB,fixed,op]
    · have coldHigh : c true = !d := by cases e : c true <;> cases d <;> simp_all
      apply beforeNext hp bud all
      have same : binary d a b = b := by
        funext x j
        cases j <;> simp [binary,hc,cold,coldHigh,op_cold]
      rw [same]; exact Or.inl (Or.inr rb)

theorem lowMix {l : List Gate} {a b : F} (d : Bool)
    (h : lowConst a) (h' : restricted l b) : restricted l (binary d a b) := by
  obtain ⟨c,hc⟩ := h
  rcases h' with ⟨v,hv⟩ | r
  · exact Or.inl ⟨op d c v,fun x => by simp [binary,hc,hv]⟩
  · by_cases e : c = d
    · exact Or.inl ⟨d,fun x => by simp [binary,hc,e,op_hot]⟩
    · have ne : c = !d := by cases c <;> cases d <;> simp_all
      have same : low (binary d a b) = low b := by
        funext x j
        simp [low,binary,hc,ne,op_cold]
      exact Or.inr (same ▸ r)

theorem addBin {k : ℕ} {s : Pool} {a b : F} (h : Stage k s) (d : Bool) (ha : s a) (hb : s b) :
    Stage (k+1) (plus s (binary d a b)) := by
  rcases h with ⟨p,hp,bud,all⟩ | ⟨p,t,l,i,flag,hi,hp,ht,hl,bud,lb,all⟩ | ⟨l,hl,lb,all⟩
  ·
    rcases all a ha with pa | ra <;> rcases all b hb with pb | rb
    · obtain ⟨u,mu,hu⟩ := pa
      obtain ⟨v,mv,hv⟩ := pb
      apply beforeNext hp bud all
      refine Or.inl (Or.inl ⟨fun j => op d (u j) (v j), ?_, fun x j => by simp [binary,hu,hv]⟩)
      cases huf : u false <;> cases hut : u true <;> cases hvf : v false <;> cases hvt : v true <;>
        cases d <;> simp_all [op]
    · exact mix d hp bud all pa rb
    · rw [bin_comm d a b]
      exact mix d hp bud all pb ra
    · exact beforeNext hp bud all (Or.inr (builds_bin (base_len p) d ra rb))
  ·
    rcases all a ha with ca | ⟨ra,la⟩ <;> rcases all b hb with cb | ⟨rb,lb'⟩
    · exact afterDrop hl lb all (lowMix d ca (Or.inl cb))
    · exact afterDrop hl lb all (lowMix d ca (Or.inr lb'))
    · rw [bin_comm d a b]
      exact afterDrop hl lb all (lowMix d cb (Or.inr la))
    · exact afterBuild hi hp ht hl bud lb all (builds_bin (joint_len p t i flag) d ra rb)
          (builds_bin (fixed_len l) d la lb')
  ·
    rcases all a ha with ca | la <;> rcases all b hb with cb | lb'
    · exact cheapNext hl lb all (Or.inl (lowMix d ca (Or.inl cb)))
    · exact cheapNext hl lb all (Or.inl (lowMix d ca (Or.inr lb')))
    · rw [bin_comm d a b]
      exact cheapNext hl lb all (Or.inl (lowMix d cb (Or.inr la)))
    · exact cheapNext hl lb all (Or.inr (builds_bin (fixed_len l) d la lb'))

theorem addNeg {k : ℕ} {s : Pool} {a : F} (h : Stage k s) (ha : s a) :
    Stage (k+1) (plus s (neg a)) := by
  rcases h with ⟨p,hp,bud,all⟩ | ⟨p,t,l,i,flag,hi,hp,ht,hl,bud,lb,all⟩ | ⟨l,hl,lb,all⟩
  ·
    rcases all a ha with ⟨c,_,hc⟩ | ra
    · apply beginSwitch 0 true (by simp [sz]) hp bud all
      exact Or.inl ⟨!(c false), fun x => by simp [neg,hc]⟩
    · exact beforeNext hp bud all (Or.inr (builds_neg (base_len p) ra))
  ·
    rcases all a ha with ⟨c,hc⟩ | ⟨ra,la⟩
    · exact afterDrop hl lb all (Or.inl ⟨!c,fun x => by simp [neg,hc]⟩)
    · exact afterBuild hi hp ht hl bud lb all (builds_neg (joint_len p t i flag) ra)
        (builds_neg (fixed_len l) la)
  ·
    rcases all a ha with ⟨c,hc⟩ | la
    · exact cheapNext hl lb all (Or.inl (Or.inl ⟨!c,fun x => by simp [neg,hc]⟩))
    · exact cheapNext hl lb all (Or.inr (builds_neg (fixed_len l) la))

theorem addConst {k : ℕ} {s : Pool} (h : Stage k s) (b : Bool) :
    Stage (k+1) (plus s (fun _ _ => b)) := by
  have pc : pureB (fun _ _ => b) := ⟨fun _ => b, fun h => h, fun _ _ => rfl⟩
  rcases h with ⟨p,hp,bud,all⟩ | ⟨p,t,l,i,flag,hi,hp,ht,hl,bud,lb,all⟩ | ⟨l,hl,lb,all⟩
  · exact beforeNext hp bud all (Or.inl (Or.inl pc))
  · exact afterDrop hl lb all (Or.inl (pure_low pc))
  · exact cheapNext hl lb all (Or.inl (Or.inl (pure_low pc)))

theorem addCopy {k : ℕ} {s : Pool} {a : F} (h : Stage k s) (ha : s a) : Stage (k+1) (plus s a) := by
  rcases h with ⟨p,hp,bud,all⟩ | ⟨p,t,l,i,flag,hi,hp,ht,hl,bud,lb,all⟩ | ⟨l,hl,lb,all⟩
  · exact beforeNext hp bud all (Or.inl (all a ha))
  ·
    exact afterDrop hl lb all ((all a ha).imp id And.right)
  · exact cheapNext hl lb all (Or.inl (all a ha))


def gfun (g : Gate) (w : Bank) : F := fun x b => g.op.eval (g.inputs.map fun i => readB w i x b)

theorem evalStage {k : ℕ} {s : Pool} {w : Bank} (g : Gate) (ok : gateOK g)
    (hs : Stage k s) (hw : ∀ i, s (readB w i)) : Stage (k+1) (plus s (gfun g w)) := by
  obtain ⟨o,ins⟩ := g
  obtain ⟨ho,hlen⟩ := ok
  change o = GateOp.and ∨ o = GateOp.or ∨ o = GateOp.not at ho
  change ins.length ≤ 2 at hlen
  rcases ho with rfl | rfl | rfl
  · cases ins with
    | nil => exact addConst hs true
    | cons i rest =>
      cases rest with
      | nil =>
        have he : gfun ⟨.and,[i]⟩ w = readB w i := by funext x b; simp [gfun,GateOp.eval]
        rw [he]; exact addCopy hs (hw i)
      | cons j rest =>
        have he : rest = [] := by simpa using hlen
        subst rest
        have eq : gfun ⟨.and,[i,j]⟩ w = binary false (readB w i) (readB w j) := by
          funext x b; simp [gfun,GateOp.eval,binary,op]
        rw [eq]; exact addBin hs false (hw i) (hw j)
  · cases ins with
    | nil => exact addConst hs false
    | cons i rest =>
      cases rest with
      | nil =>
        have he : gfun ⟨.or,[i]⟩ w = readB w i := by funext x b; simp [gfun,GateOp.eval]
        rw [he]; exact addCopy hs (hw i)
      | cons j rest =>
        have he : rest = [] := by simpa using hlen
        subst rest
        have eq : gfun ⟨.or,[i,j]⟩ w = binary true (readB w i) (readB w j) := by
          funext x b; simp [gfun,GateOp.eval,binary,op]
        rw [eq]; exact addBin hs true (hw i) (hw j)
  · cases ins with
    | nil => exact addConst hs true
    | cons i _ => exact addNeg hs (hw i)

theorem later {n : ℕ} {w : Bank} (len : ∀ x b, (w x b).length = n) (g : Gate) (i : ℕ) (hn : i ≠ n) :
    readB (extend w g) i = readB w i := by
  funext x b
  by_cases lt : i < n
  · exact List.getD_append _ _ _ _ (by rw [len]; exact lt)
  · change (w x b ++ [_]).getD i false = (w x b).getD i false
    rw [List.getD_eq_default _ _ (by simp [len]; omega),List.getD_eq_default _ _ (by rw [len]; omega)]

theorem process (gs : List Gate) (ok : good gs) {n k : ℕ} {s : Pool} {w : Bank}
    (len : ∀ x b, (w x b).length = n) (hs : Stage k s) (hw : ∀ i, s (readB w i)) :
    ∃ v : Pool, Stage (k+gs.length) v ∧ ∀ i, v (readB (fun x b => run gs (w x b)) i) := by
  induction gs generalizing n k s w with
  | nil => exact ⟨s,by simpa using hs,hw⟩
  | cons g rest ih =>
    let next := plus s (gfun g w)
    have hnext : Stage (k+1) next := evalStage g (ok g List.mem_cons_self) hs hw
    have wires (i : ℕ) : next (readB (extend w g) i) := by
      by_cases e : i = n
      · subst i
        exact Or.inr (funext fun x => funext fun b => lastRead len g x b)
      · exact Or.inl (later len g i e ▸ hw i)
    obtain ⟨v,stage,hv⟩ := ih (fun a ha => ok a (List.mem_cons_of_mem _ ha))
      (n := n+1) (fun x b => by simp [extend,step,len]) hnext wires
    exact ⟨v,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using stage,hv⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def seed (x : X) (b : Bool) : List Bool :=
  [x 1, x 0, x 4, x 7, x 5, x 2, b, x 6, x 3, x 1 || b]

theorem start (i : ℕ) : ahead [] (readB seed i) := by
  by_cases h : i < 10
  · interval_cases i
    · exact Or.inr ⟨1, by decide, rfl⟩
    · exact Or.inr ⟨0, by decide, rfl⟩
    · exact Or.inr ⟨4, by decide, rfl⟩
    · exact Or.inr ⟨7, by decide, rfl⟩
    · exact Or.inr ⟨5, by decide, rfl⟩
    · exact Or.inr ⟨2, by decide, rfl⟩
    · exact Or.inl ⟨id, by decide, fun _ _ => rfl⟩
    · exact Or.inr ⟨6, by decide, rfl⟩
    · exact Or.inr ⟨3, by decide, rfl⟩
    · exact Or.inr ⟨8, by decide, rfl⟩
  · refine Or.inl ⟨fun _ => false, by decide, fun x b => ?_⟩
    exact List.getD_eq_default _ _ (by simp [seed]; omega)

def result (lo hi : X → Bool) : Prop :=
  HasCircuitSize 8 lo 12 ∨ ∃ (p t : Circuit) (i : Nat),
    FanInTwo p ∧ FanInTwo t ∧ p.size + t.size ≤ 13 ∧
    let w := fun (b : Bool) (x : X) => p.wires (List.ofFn x ++ [x 1 || b])
    (∀ x, t.eval (w false x ++ [(w false x).getD i false]) = lo x) ∧
    ∀ x, t.eval (w true x ++ [true]) = hi x

theorem constantCore {lo : X → Bool} (c : Bool) (h : ∀ x, lo x = c) : HasCircuitSize 8 lo 12 := by
  cases c
  · refine ⟨(⟨[],8⟩ : Circuit), ?_, by decide, ?_⟩
    · intro g hg
      change g ∈ ([] : List Gate) at hg
      cases hg
    · intro x
      rw [h]
      change (List.ofFn x).getD 8 false = false
      exact List.getD_eq_default _ _ (by simp)
  · refine ⟨⟨[⟨.and,[]⟩],8⟩,?_,by decide,?_⟩
    · intro g hg
      have e : g = ⟨.and,[]⟩ := List.mem_singleton.mp hg
      subst g
      simp
    · intro x
      rw [h]
      change (List.ofFn x ++ [true]).getD 8 false = true
      rw [List.getD_append_right _ _ _ _ (by simp)]
      simp

theorem finish {k : ℕ} {s : Pool} {f : F} {lo hi : X → Bool} (hk : k ≤ 14)
    (hs : Stage k s) (haveOut : s f) (he : ∀ x b, f x b = if b then hi x else lo x)
    (switches : ∃ x : X, x 1 = true ∧ lo x = false ∧ hi x = true) : result lo hi := by
  have constEnd (h : lowConst f) : result lo hi := by
    obtain ⟨c,hc⟩ := h
    exact Or.inl (constantCore c (fun x => (he x false).symm.trans (hc x)))
  rcases hs with ⟨p,hp,bud,all⟩ | ⟨p,t,l,i,d,h,hp,ht,hl,bud,lb,all⟩ | ⟨l,hl,bud,all⟩
  · rcases all f haveOut with h | ⟨i,_,rfl⟩
    · exact constEnd (pure_low h)
    · obtain ⟨x,hx,hlo,hhi⟩ := switches
      have eq : readB (base p) i x false = readB (base p) i x true := by simp [readB, base, hx]
      have bad : lo x = hi x := (he x false).symm.trans (eq.trans (he x true))
      simp [hlo,hhi] at bad
  · rcases all f haveOut with c | ⟨⟨j,_,rfl⟩,_⟩
    · exact constEnd c
    · refine Or.inr ⟨⟨p,0⟩,⟨t,j⟩,i,hp,ht,?_,?_,?_⟩
      · change p.length+t.length ≤ 13
        omega
      · intro x
        exact he x false
      · intro x
        exact he x true
  · rcases all f haveOut with c | ⟨i,_,hr⟩
    · exact constEnd c
    · let D : Circuit := ⟨l,i⟩
      refine Or.inl ⟨collapseCircuit D, collapsed_fan (C := D) hl, ?_, ?_⟩
      · rw [collapsed_size]
        change l.length ≤ 12
        omega
      · intro x
        rw [collapsed_eval]
        have eq := (congrFun (congrFun hr x) false).trans (he x false)
        simpa [D, Circuit.eval, Circuit.wires, readB, fixed, base] using eq

theorem solve (C : Circuit) (lo hi : X → Bool) (fan : FanInTwo C) (small : C.size ≤ 14)
    (spec : ∀ (b : Bool) (x : X), C.eval (seed x b) = if b then hi x else lo x)
    (switches : ∃ x : X, x 1 = true ∧ lo x = false ∧ hi x = true) : result lo hi := by
  let s : Pool := ahead []
  have hs : Stage 0 s := .before [] (by intro a h; cases h) (by decide) (fun _ h => h)
  obtain ⟨v, hv, avail⟩ := process C.gates fan
    (fun x b => show (seed x b).length = 10 from rfl) hs start
  apply finish (s := v) (by simpa [Circuit.size] using small) hv (avail C.output) _ switches
  exact fun x b => spec b x

end PEqualNP.Outside.L_meta_3102

theorem PEqualNP.Outside.L_meta_3102 : have x1 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x1 : Bool) (x2 : Fin (8 : ℕ) → Bool) => [x2 (1 : Fin (8 : ℕ)), x2 (0 : Fin (8 : ℕ)), x2 (4 : Fin (8 : ℕ)), x2 (7 : Fin (8 : ℕ)), x2 (5 : Fin (8 : ℕ)), x2 (2 : Fin (8 : ℕ)), x1, x2 (6 : Fin (8 : ℕ)), x2 (3 : Fin (8 : ℕ)), x2 (1 : Fin (8 : ℕ)) || x1]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : (Fin (8 : ℕ) → Bool) → Bool),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (14 : ℕ) →       (∀ (x7 : Bool) (x8 : Fin (8 : ℕ) → Bool), x2.eval (x1 x7 x8) = if x7 = Bool.true then x4 x8 else x3 x8) →         (∃ (x8 : Fin (8 : ℕ) → Bool), x8 (1 : Fin (8 : ℕ)) = Bool.true ∧ x3 x8 = Bool.false ∧ x4 x8 = Bool.true) →           PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) x3 (12 : ℕ) ∨             ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : PEqualNP.CircuitLowerBounds.Circuit) (x11 : ℕ),               PEqualNP.MetaComplexity.FanInTwo x9 ∧                 PEqualNP.MetaComplexity.FanInTwo x10 ∧                   x9.size + x10.size ≤ (13 : ℕ) ∧                     have x12 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x12 : Bool) (x13 : Fin (8 : ℕ) → Bool) => x9.wires (List.ofFn x13 ++ [x13 (1 : Fin (8 : ℕ)) || x12]);                     (∀ (x13 : Fin (8 : ℕ) → Bool), x10.eval (x12 Bool.false x13 ++ [(x12 Bool.false x13).getD x11 Bool.false]) = x3 x13) ∧ ∀ (x13 : Fin (8 : ℕ) → Bool), x10.eval (x12 Bool.true x13 ++ [Bool.true]) = x4 x13 := PEqualNP.Outside.L_meta_3102.solve
