import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4849

namespace Refute4848

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : List (Fin 8 × Fin 8) :=
  [(0,4),(0,6),(1,5),(1,6),(1,7),(2,6),(3,7),(4,7)]

def adjacent (u v : Fin 8) : Bool :=
  edges.contains (u,v) || edges.contains (v,u)

def graph : SimpleGraph (Fin 8) :=
  SimpleGraph.mk' ⟨adjacent,
    (by decide +kernel : (∀ a b, adjacent a b = adjacent b a) ∧
      (∀ a, ¬ adjacent a a))⟩

instance : DecidableRel graph.Adj :=
  fun a b => inferInstanceAs (Decidable (adjacent a b = true))

def witness : Circuit :=
  ⟨[⟨.or,[3,4]⟩,⟨.or,[4,6]⟩,⟨.and,[8,7]⟩,⟨.or,[10,1]⟩,
    ⟨.or,[6,7]⟩,⟨.and,[2,12]⟩,⟨.or,[0,13]⟩,⟨.and,[14,9]⟩,
    ⟨.or,[5,12]⟩,⟨.and,[11,16]⟩,⟨.or,[15,17]⟩],18⟩

def bitsAdj (u v : Fin 8) : Bool := (0x1a0702818040e050 : Nat).testBit (8*u.val+v.val)
theorem adjBits : ∀ u v : Fin 8,graph.Adj u v ↔ bitsAdj u v=true := by decide +kernel

theorem noTriangle : ∀ (a b c : Fin 8), graph.Adj a b → graph.Adj b c → ¬ graph.Adj c a := by
  have fast : ∀ a b c : Fin 8,bitsAdj a b=true → bitsAdj b c=true → ¬bitsAdj c a=true := by decide +kernel
  simpa only [adjBits] using fast

theorem noFour : PEqualNP.TopForm.NoFourCycle graph := by
  have fast : ∀ a b : Fin 8,a≠b →
      (Finset.univ.filter fun w=>bitsAdj a w=true ∧ bitsAdj b w=true).card ≤ 1 := by decide +kernel
  intro a b ne
  have eq : (Finset.univ.filter fun w=>graph.Adj a w ∧ graph.Adj b w) =
      (Finset.univ.filter fun w=>bitsAdj a w=true ∧ bitsAdj b w=true) := by
    ext w
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,adjBits]
  rw [eq]
  exact fast a b ne

theorem mono : Monotone2 witness := by
  intro g belongs
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at belongs
  rcases belongs with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp

theorem size_eq : witness.size = 11 := rfl
theorem badIndex : 5 < witness.gates.length := by decide
theorem badOp : (NestedCover.gateAt witness 5).op = GateOp.and := rfl
theorem badInput :
    PEqualNP.EdgeOwnership.gateVal 8 witness 5 (PEqualNP.EdgeOwnership.pairInput 2 7) = true := by
  decide +kernel
theorem noEdge : ¬ graph.Adj 2 7 := by decide +kernel

theorem graph_any (x : Fin 8→Bool) :
    NestedCover.graphFun graph ∅ x=edges.any (fun uv=>x uv.1 && x uv.2) := by
  apply Bool.eq_iff_iff.mpr
  simp only [NestedCover.graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,
    Bool.false_or,decide_eq_true_eq,List.any_eq_true,Bool.and_eq_true]
  constructor
  · rintro ⟨u,v,h,hu,hv⟩
    change adjacent u v=true at h
    rcases Bool.or_eq_true_iff.mp h with direct|back
    · exact ⟨(u,v),List.contains_iff_mem.mp direct,hu,hv⟩
    · exact ⟨(v,u),List.contains_iff_mem.mp back,hv,hu⟩
  · rintro ⟨⟨u,v⟩,mem,hu,hv⟩
    refine ⟨u,v,?_,hu,hv⟩
    change ((edges.contains (u,v)) || edges.contains (v,u))=true
    exact Bool.or_eq_true_iff.mpr (Or.inl (List.contains_iff_mem.mpr mem))

def eFormula (a b c d e f g h : Bool) :=
  a && e || a && g || b && f || b && g || b && h || c && g || d && h || e && h

def wFormula (a b c d e f g h : Bool) :=
  ((a || c && (g || h)) && (e || g)) || ((((d || e) && h) || b) && (f || (g || h)))

theorem circuits_agree : ∀ a b c d e f g h : Bool,wFormula a b c d e f g h=eFormula a b c d e f g h := by
  decide +kernel

theorem eval_formula (a b c d e f g h : Bool) : witness.eval [a,b,c,d,e,f,g,h]=wFormula a b c d e f g h := by
  simp [witness,Circuit.eval,Circuit.wires,GateOp.eval,List.getD_eq_getElem?_getD,wFormula]

theorem outcome_formula (x : Fin 8→Bool) :
    edges.any (fun uv=>x uv.1 && x uv.2)=eFormula (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) := by
  simp [edges,eFormula,Bool.or_assoc]

theorem computes : circuitFun 8 witness = NestedCover.graphFun graph ∅ := by
  funext x
  rw [graph_any,outcome_formula]
  have entries : List.ofFn x=[x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7] := rfl
  change witness.eval (List.ofFn x)=_
  rw [entries,eval_formula,circuits_agree]

end Refute4848

namespace Refute4848.Solver
abbrev Row := Fin 43
abbrev Sig := BitVec 43
def read (x : Row) (a : Sig) : Bool := a.getLsbD x.val
def zero : Sig := 0
def one : Sig := BitVec.allOnes 43
class Goal where
  fn : Sig
  yes : ∃ r : Row, read r fn = true
  no : ∃ r : Row, read r fn = false
abbrev target [g : Goal] : Sig := g.fn
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b

lemma zero_read (x : Row) : read x zero = false := by simp [read, zero]
lemma one_read (x : Row) : read x one = true := by
  rw [read,one,BitVec.getLsbD_allOnes]
  exact decide_eq_true x.isLt
lemma neg_read (x : Row) (a : Sig) : read x (neg a) = !(read x a) := by
  simp [read,neg,x.isLt]
lemma bin_read (x : Row) (a b : Sig) (d : Bool) :
    read x (bin d a b) = (if d then read x a || read x b else read x a && read x b) := by
  cases d <;> simp [read, bin]

-- Full truth tables have no padding bits, so every function is a valid signature.
abbrev Valid (_ : Sig) : Prop := True
def proper (a : Sig) := Valid a ∧ a ≠ zero ∧ a ≠ one
theorem valid_zero : Valid zero := trivial
theorem valid_one : Valid one := trivial
theorem valid_bin {a b : Sig} (_ : Valid a) (_ : Valid b) {d : Bool} : Valid (bin d a b) := trivial
theorem valid_neg {a : Sig} (_ : Valid a) : Valid (neg a) := trivial

theorem bin_comm {d : Bool} (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.or_comm,BitVec.and_comm]
theorem bin_laws {a : Sig} (_ : Valid a) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a :=
  ⟨BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,
    BitVec.and_self,BitVec.or_self⟩
theorem neg_laws : neg zero = one ∧ neg one = zero := by decide
theorem target_proper [g : Goal] : proper target := by
  refine ⟨trivial,?_,?_⟩
  · intro h
    obtain ⟨r,b⟩ := g.yes
    have eq := congrArg (read r) h
    change read r g.fn = read r _ at eq
    simp only [zero_read,one_read] at eq
    rw [eq] at b
    contradiction
  · intro h
    obtain ⟨r,b⟩ := g.no
    have eq := congrArg (read r) h
    change read r g.fn = read r _ at eq
    simp only [zero_read,one_read] at eq
    rw [eq] at b
    contradiction
inductive Live [g : Goal] : Nat → Nat → Finset Sig → Prop
  | stop : Live 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)) :
      Live (k + 1) (t + 1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)) :
      Live (k + 1) t (insert a (insert b U))
variable [goalData : Goal]

lemma live_proper {k t S} (h : Live k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop => simpa using target_proper
  | unary ha _ _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb _ _ _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha, hb, fun a h => ih a (Finset.mem_insert_of_mem h)⟩
lemma live_size {k t S} (h : Live k t S) : t ≤ k ∧ S.card + t ≤ k + 1 := by
  induction h with
  | stop => simp
  | @unary k t U a _ hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega, by omega⟩
  | @binary k t U a b d _ _ _ hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega, by omega⟩

end Refute4848.Solver

namespace Finite4848

abbrev Sig := BitVec 43
def goal : Sig := 255
def basis : List Sig := [0x12012049503,0x95261c,0x14054a63820,0x958c7c040,0xa60f80081,
  0x58c7f000004,0x60f8000002a,0x7f0000000d0]

def missing (p : Nat) : List Sig → Sig
  | [] => BitVec.allOnes 43
  | a :: as => if a.getLsbD p then a &&& missing p as else missing p as

def canSeparate (pool : List Sig) : Bool :=
  (List.range 8).all (fun p => (missing p pool &&& ~~~goal) == 0)

def nextPools (pool : List Sig) (a b z : Sig) : List (List Sig) :=
  let rest := pool.filter (fun w => w != a && w != b)
  [z :: rest, z :: a :: rest, z :: b :: rest, z :: a :: b :: rest]

def successors (pool : List Sig) (budget : Nat) : List (List Sig) :=
  pool.flatMap fun a => pool.flatMap fun b =>
    if a.toNat < b.toNat then
      [a &&& b, a ||| b].flatMap fun z =>
        if pool.contains z then [] else
          (nextPools pool a b z).filter (fun t => t.length ≤ budget+1 && canSeparate t)
    else []

def search : Nat → List Sig → Bool
  | 0, pool => pool.contains goal
  | k+1, pool => pool.contains goal || (successors pool k).any (search k)


end Finite4848

namespace Refute4848.Search
open Refute4848.Solver
open Finite4848 (basis goal missing canSeparate nextPools successors search)

instance : Goal := ⟨goal,⟨0,by decide⟩,⟨8,by decide⟩⟩

theorem live_preserves_pair {k t : Nat} {pool : Finset Sig} (live : Live k t pool)
    (noNeg : t=0) (p q : Row)
    (available : ∀ a∈pool, read p a = true → read q a = true) :
    read p target = true → read q target = true := by
  induction live with
  | stop => exact available _ (by simp)
  | unary => omega
  | @binary k t u a b d ha hb diff fresh tail ih =>
    apply ih noNeg
    intro w hw hp
    rcases Finset.mem_insert.mp hw with rfl|other
    · rw [bin_read] at hp ⊢
      have orderedA := available a (by simp)
      have orderedB := available b (by simp)
      cases d
      · obtain ⟨h1,h2⟩ := Bool.and_eq_true_iff.mp hp
        exact Bool.and_eq_true_iff.mpr ⟨orderedA h1,orderedB h2⟩
      · rcases Bool.or_eq_true_iff.mp hp with h|h
        · exact Bool.or_eq_true_iff.mpr (Or.inl (orderedA h))
        · exact Bool.or_eq_true_iff.mpr (Or.inr (orderedB h))
    · exact available _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem other)) hp

theorem live_separates {k : Nat} {pool : Finset Sig} (live : Live k 0 pool)
    {p q : Row} (yes : read p target = true) (no : read q target = false) :
    ∃ a∈pool, read p a=true ∧ read q a=false := by
  classical
  by_contra absent
  have forward : ∀ a∈pool, read p a = true → read q a = true := by
    intro a ha h
    cases actual : read q a
    · exact (absent ⟨a,ha,h,actual⟩).elim
    · rfl
  have impossible := live_preserves_pair live rfl p q forward yes
  rw [no] at impossible
  contradiction

theorem missing_bit {ws : List Sig} {w : Sig} (has : w ∈ ws) (p q : Row)
    (yes : read p w = true) (no : read q w = false) :
    read q (missing p.val ws) = false := by
  induction ws with
  | nil => simp at has
  | cons a as ih =>
    rcases List.mem_cons.mp has with rfl|hs
    · change w.getLsbD p.val = true at yes
      change w.getLsbD q.val = false at no
      change (missing p.val (w::as)).getLsbD q.val = false
      rw [missing,if_pos yes,BitVec.getLsbD_and,no]
      rfl
    · have inherited := ih hs
      change (missing p.val as).getLsbD q.val = false at inherited
      change (missing p.val (a::as)).getLsbD q.val = false
      by_cases h : a.getLsbD p.val = true
      · rw [missing,if_pos h,BitVec.getLsbD_and,inherited]
        exact Bool.and_false _
      · rw [missing,if_neg h]
        exact inherited

theorem positives (p : Row) (small : p.val < 8) : read p target = true := by
  have only : ∀ p : Row, p.val < 8 → read p target = true := by decide +kernel
  exact only p small

theorem canSeparate_of_live {k : Nat} {ws : List Sig} (live : Live k 0 ws.toFinset) :
    canSeparate ws = true := by
  apply List.all_eq_true.mpr
  intro j hj
  have small := List.mem_range.mp hj
  let p : Row := ⟨j,by omega⟩
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  let q : Row := ⟨r,hr⟩
  have eq : ((missing p.val ws &&& ~~~goal).getLsbD q.val) = (0 : Sig).getLsbD q.val := by
    cases hq : read q target with
    | false =>
      obtain ⟨a, ha, hap, haq⟩ := live_separates live (positives p small) hq
      have mw := missing_bit (List.mem_toFinset.mp ha) p q hap haq
      rw [BitVec.getLsbD_and,show (missing p.val ws).getLsbD q.val = false from mw]
      exact (zero_read q).symm
    | true =>
      have hg : goal.getLsbD q.val = true := hq
      simp only [BitVec.getLsbD_and,BitVec.getLsbD_not,hg,Bool.not_true,Bool.and_false]
      exact (zero_read q).symm
  exact eq

end Refute4848.Search

namespace Refute4848.Search
open Refute4848.Solver
open Finite4848 (basis goal missing canSeparate nextPools successors search)

theorem legalNext {ws : List Sig} {other : Finset Sig} {a b z : Sig}
    (eq : ws.toFinset = insert a (insert b other)) (nd : ws.Nodup)
    (diff : a ≠ b) (fresh : z ∉ ws) :
    ∃ next ∈ nextPools ws a b z, next.toFinset = insert z other ∧ next.Nodup := by
  classical
  let rest := ws.filter (fun w => w != a && w != b)
  have aNot : a ∉ rest := by simp [rest]
  have bNot : b ∉ rest := by simp [rest]
  have rNd : rest.Nodup := nd.filter _
  have zNot : z ∉ rest := fun h => fresh (List.mem_filter.mp h).1
  have za : z ≠ a := by
    intro h; apply fresh
    have ha : a ∈ ws.toFinset := by simp [eq]
    simpa [h] using List.mem_toFinset.mp ha
  have zb : z ≠ b := by
    intro h; apply fresh
    have hb : b ∈ ws.toFinset := by simp [eq]
    simpa [h] using List.mem_toFinset.mp hb
  let keep := (if a ∈ other then [a] else []) ++ (if b ∈ other then [b] else [])
  let nxt := z :: (keep ++ rest)
  have choices : nxt ∈ nextPools ws a b z := by
    by_cases ha : a ∈ other <;> by_cases hb : b ∈ other <;>
      simp [nxt,keep,ha,hb,nextPools,rest]
  have matchRest (w : Sig) : w ∈ rest ↔ w ∈ other ∧ w ≠ a ∧ w ≠ b := by
    have old : w ∈ ws ↔ w ∈ insert a (insert b other) := by
      rw [← eq,List.mem_toFinset]
    simp only [rest,List.mem_filter,Bool.and_eq_true,bne_iff_ne,old,Finset.mem_insert]
    tauto
  have matchKeep (w : Sig) : w ∈ keep ↔ w∈other ∧ (w=a ∨ w=b) := by
    have member (v : Sig) : w ∈ (if v ∈ other then [v] else []) ↔
        w=v ∧ v∈other := by
      by_cases h : v∈other <;> simp [h]
    simp only [keep,List.mem_append,member]
    constructor
    · rintro (⟨rfl,h⟩|⟨rfl,h⟩) <;> exact ⟨h,by simp⟩
    · rintro ⟨h,rfl|rfl⟩ <;> simp [h]
  refine ⟨nxt,choices,?_,?_⟩
  · ext w
    simp only [nxt, List.mem_toFinset,List.mem_cons,List.mem_append,
      matchKeep,matchRest,Finset.mem_insert]
    tauto
  · by_cases ha : a ∈ other <;> by_cases hb : b ∈ other <;>
      simp [nxt,keep,ha,hb,rNd,aNot,bNot,zNot,diff,za,zb]

theorem step_search {rem k : Nat} {ws : List Sig} {u : Finset Sig} {a b : Sig} {d : Bool}
    (lt : a.toNat < b.toNat) (eq : ws.toFinset = insert a (insert b u)) (nd : ws.Nodup)
    (fresh : bin d a b ∉ insert a (insert b u))
    (tail : Live k 0 (insert (bin d a b) u)) (bound : k ≤ rem)
    (survives : ∀ w : List Sig, w.Nodup → w.toFinset = insert (bin d a b) u →
      search rem w = true) :
    search (rem+1) ws = true := by
  have aIn : a ∈ ws := List.mem_toFinset.mp (by simp [eq])
  have bIn : b ∈ ws := List.mem_toFinset.mp (by simp [eq])
  have zNew : bin d a b ∉ ws := fun h => fresh (eq ▸ List.mem_toFinset.mpr h)
  obtain ⟨n, hn, eqn, nn⟩ := legalNext eq nd (fun h => (lt.ne (congrArg BitVec.toNat h)).elim) zNew
  have child : Live k 0 n.toFinset := eqn.symm ▸ tail
  have total : n.length ≤ rem+1 := by
    have bound' := (live_size child).2
    rw [List.toFinset_card_of_nodup nn] at bound'
    omega
  have can := canSeparate_of_live child
  have hz : bin d a b ∈ [a &&& b,a ||| b] := by cases d <;> simp [bin]
  have it : n ∈ successors ws rem := by
    unfold successors
    apply List.mem_flatMap.mpr
    refine ⟨a,aIn,List.mem_flatMap.mpr ⟨b,bIn,?_⟩⟩
    simp only [lt,if_true]
    apply List.mem_flatMap.mpr
    refine ⟨_,hz,?_⟩
    simp [zNew,hn,total,can]
  exact Bool.or_eq_true_iff.mpr (Or.inr (List.any_eq_true.mpr ⟨n,it,survives n nn eqn⟩))

theorem search_complete (budget : Nat) {k : Nat} (bound : k ≤ budget)
    {pool : Finset Sig} (live : Live k 0 pool)
    {ws : List Sig} (eq : ws.toFinset = pool) (nd : ws.Nodup) :
    search budget ws = true := by
  induction budget generalizing k pool ws with
  | zero =>
    have hk : k=0 := by omega
    subst k
    cases live
    have ht : (goal : Sig) = target := rfl
    apply List.contains_iff_mem.mpr
    apply List.mem_toFinset.mp
    rw [eq,ht]
    exact Finset.mem_singleton_self _
  | succ rem ih =>
    cases live with
    | stop =>
      have ht : (goal : Sig) = target := rfl
      have old : goal ∈ ws := List.mem_toFinset.mp (by rw [eq,ht]; exact Finset.mem_singleton_self _)
      simp [search,List.contains_iff_mem,old]
    | @binary k _ u a b d ha hb diff fresh tail =>
      have low : k ≤ rem := by omega
      rcases lt_or_gt_of_ne (fun h : a.toNat = b.toNat => diff (BitVec.eq_of_toNat_eq h)) with lt|gt
      · exact step_search lt eq nd fresh tail low (fun s hn hs => ih low tail hs hn)
      · have eq' : ws.toFinset = insert b (insert a u) := by rw [eq,Finset.insert_comm]
        have swap : bin d b a = bin d a b := by cases d <;> simp [bin,BitVec.or_comm,BitVec.and_comm]
        have fresh' : bin d b a ∉ insert b (insert a u) := by
          rwa [swap,Finset.insert_comm]
        have tail' : Live k 0 (insert (bin d b a) u) := by rwa [swap]
        exact step_search gt eq' nd fresh' tail' low (fun s hn hs => ih low tail' hs hn)

end Refute4848.Search

namespace Refute4848.Solver
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
variable [goalData : Goal]

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero
def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w
lemma valid_getD {w : List Sig} (hw : ∀ a ∈ w, Valid a) (i : Nat) : Valid (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact valid_zero
  | some a => exact hw a (List.mem_of_getElem? h)
lemma gv_valid {w : List Sig} (hw : ∀ a ∈ w, Valid a) (g : Gate) : Valid (gv w g) := by
  obtain ⟨o, l⟩ := g
  cases o with
  | and =>
    change Valid ((l.map (fun i => w.getD i zero)).foldr (bin false) one)
    induction l with
    | nil => exact valid_one
    | cons i l ih => exact valid_bin (valid_getD hw i) ih
  | or =>
    change Valid ((l.map (fun i => w.getD i zero)).foldr (bin true) zero)
    induction l with
    | nil => exact valid_zero
    | cons i l ih => exact valid_bin (valid_getD hw i) ih
  | not =>
    cases l with
    | nil => exact valid_neg valid_zero
    | cons i _ => exact valid_neg (valid_getD hw i)
  | mod _ => exact valid_zero
  | maj => exact valid_zero
def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬ proper v
lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.2.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)
lemma operand_cases {w : List Sig} {a : Sig} (hva : Valid a) (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hva, hz, ho⟩), hva, hz, ho⟩)
def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)
lemma bin_rep {w a b} (d : Bool) (hva : Valid a) (hvb : Valid b)
    (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.2.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2.2 rfl)
  obtain ⟨a1, a0, az, ao, aa, aa'⟩ := bin_laws hva
  obtain ⟨b1, b0, bz, bo, bb, bb'⟩ := bin_laws hvb
  rcases operand_cases hva ha with rfl | rfl | ⟨ham, hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hvb hb with rfl | rfl | ⟨hbm, hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a = b
  · subst b; cases d <;> simp_all
  exact Or.inr ⟨d, a, b, ham, hbm, hap, hbp, he, rfl⟩
lemma gate_rep {w : List Sig} (hw : ∀ a ∈ w, Valid a) (g : Gate)
    (h : (g.op=.and ∨ g.op=.or) ∧ g.inputs.length ≤ 2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o, l⟩ := g
  obtain ⟨ho, hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.2.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2.2 rfl)
  cases l with
  | nil =>
    rcases ho with rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl
      · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
          (bin_laws (valid_getD hw i)).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
          (bin_laws (valid_getD hw i)).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
    | cons j l =>
      cases l with
      | cons _ _ => simp at hl
      | nil =>
        rcases ho with rfl | rfl
        · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
            (bin_laws (valid_getD hw j)).1] using
            bin_rep false (valid_getD hw i) (valid_getD hw j) (get_rep w i) (get_rep w j)
        · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
            (bin_laws (valid_getD hw j)).2.1] using
            bin_rep true (valid_getD hw i) (valid_getD hw j) (get_rep w i) (get_rep w j)
lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w ++ [z]) :
    ∃ k' S', k' ≤ k + 1 ∧ Live k' t S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k, S, by omega, h, ?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a ∈ w ∨ a = z) with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨d, a, b, ha, hb, pa, pb, hab, eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live k t (insert (bin d a b) U) := by simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv; obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hv; simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh; rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_, _, Nat.le_refl _, Live.binary pa pb hab hf ht,
          by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k, S, by omega, h, ?_⟩
    intro a ha; have hn : a ≠ z := fun hh => hm (hh ▸ ha); simpa [hn] using sub a ha
lemma extract (gs : List Gate) (w : List Sig) (hw : ∀ a ∈ w, Valid a)
    (legal : ∀ g ∈ gs, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length ≤ 2)
    (hout : target ∈ execute gs w) :
    ∃ k S, k ≤ gs.length ∧ Live k 0 S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0, {target}, by simp, Live.stop, by simpa [execute] using hout⟩
  | cons g gs ih =>
    have hw' : ∀ a ∈ w ++ [gv w g], Valid a := by
      intro a ha; rcases List.mem_append.mp ha with ha | ha
      · exact hw a ha
      · simp only [List.mem_singleton] at ha; exact ha ▸ gv_valid hw g
    obtain ⟨k, S, hk, ht, hs⟩ := ih (w ++ [gv w g]) hw' (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l, T, hl, hu, hT⟩ := pull_gate ht (gate_rep hw g (legal g (by simp))) hs
    exact ⟨l, T, by simp; omega, hu, hT⟩
theorem eval_lookup (x : Row) (w : List Sig) (i : ℕ) :
    (w.map (read x)).getD i false = read x (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[i]? <;> simp [zero_read]

private theorem andRead (x : Row) (w : List Sig) :
    read x (w.foldr (bin false) one) = (w.map (read x)).all id := by
  induction w with
  | nil => simp [one_read]
  | cons a as ih => simp [bin_read,ih]

private theorem orRead (x : Row) (w : List Sig) :
    read x (w.foldr (bin true) zero) = (w.map (read x)).any id := by
  induction w with
  | nil => simp [zero_read]
  | cons a as ih => simp [bin_read,ih]

private theorem eval_gate (x : Row) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    read x (gv w g) = g.op.eval (g.inputs.map fun i => (w.map (read x)).getD i false) := by
  simp only [eval_lookup]
  obtain ⟨op,xs⟩ := g
  have hh : op = .and ∨ op = .or ∨ op = .not := by
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using h
  rcases hh with rfl|rfl|rfl
  · simp [gv,GateOp.eval,andRead,List.map_map,Function.comp_apply] <;> rfl
  · simp [gv,GateOp.eval,orRead,List.map_map,Function.comp_apply] <;> rfl
  · cases xs <;> simp [gv,GateOp.eval,neg_read,zero_read]

theorem execute_eval (x : Row) (gs : List Gate) (w : List Sig)
    (h : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (execute gs w).map (read x) =
      gs.foldl (fun l g => l ++ [g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (read x)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w ++ [gv w g])).map _ = _
    rw [ih _ (fun a ha => h a (List.mem_cons_of_mem _ ha))]
    simp only [List.foldl_cons, List.map_append, List.map_singleton, eval_gate x w g (h g (by simp))]

theorem circuit_eval (x : Row) (C : Circuit) (w : List Sig) (hf : FanInTwo C) :
    read x ((execute C.gates w).getD C.output zero) = C.eval (w.map (read x)) := by
  rw [← eval_lookup, execute_eval x C.gates w (fun g hg => (hf g hg).1)]
  rfl

theorem circuit_extract (w : List Sig) (C : Circuit) (hf : FanInTwo C)
    (pure : ∀ g∈C.gates,g.op=.and ∨ g.op=.or)
    (he : ∀ x, C.eval (w.map (read x)) = read x target) :
    ∃ k S, k ≤ C.size ∧ Live k 0 S ∧ ∀ v ∈ S, v ∈ w := by
  have eq : (execute C.gates w).getD C.output zero = target := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    exact (circuit_eval ⟨i,hi⟩ C w hf).trans (he ⟨i,hi⟩)
  have hit : target ∈ execute C.gates w := by
    have h := get_rep (execute C.gates w) C.output
    rw [eq] at h
    exact h.resolve_right (fun hp => hp target_proper)
  exact extract _ _ (fun _ _ => trivial) (fun g hg => ⟨pure g hg,(hf g hg).2⟩) hit


end Refute4848.Solver

namespace Refute4848.Root
open Refute4848.Solver Refute4848.Search
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Finite4848 (basis goal search)

def samples : List Nat :=
  [17,65,34,66,130,68,136,144,1,2,3,4,5,6,8,9,10,12,15,16,18,20,24,30,32,33,
    36,40,45,48,60,64,72,80,96,120,128,129,132,160,165,192,224]

def assignment (r : Row) (v : Fin 8) : Bool :=
  (samples.getD r.val 0).testBit v.val

set_option maxRecDepth 15000 in
theorem sample_circuit :
    ∀ r : Row, basis.map (read r) = List.ofFn (assignment r) ∧
      circuitFun 8 witness (assignment r) = read r target := by decide +kernel

theorem sample_agreement (r : Row) :
    basis.map (read r) = List.ofFn (assignment r) ∧
      NestedCover.graphFun graph ∅ (assignment r) = read r target := by
  rw [← computes]
  exact sample_circuit r

def position (i : Fin basis.length) : Row × Row :=
  ([(0,19),(2,24),(5,31),(6,36),(0,8),(2,9),(1,8),(4,9)] : List (Row×Row)).getD i.val (0,0)

set_option maxRecDepth 13000 in
theorem essential :
    ∀ i : Fin basis.length, read (position i).1 target = true ∧
      read (position i).2 target = false ∧
      ∀ j : Fin basis.length, j ≠ i →
      read (position i).1 basis[j] = read (position i).2 basis[j] := by decide +kernel

theorem basis_nodup : basis.Nodup := by decide

theorem root_eq {k : Nat} {pool : Finset Sig} (live : Live k 0 pool)
    (within : ∀ w∈pool, w∈basis) : basis.toFinset = pool := by
  classical
  apply Finset.Subset.antisymm _ (fun w hw => List.mem_toFinset.mpr (within w hw))
  intro w mw
  obtain ⟨i, hi, ith⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp mw)
  let u : Fin basis.length := ⟨i,hi⟩
  obtain ⟨hp,hq,unchanged⟩ := essential u
  obtain ⟨a,ha,one,zero⟩ := live_separates live hp hq
  obtain ⟨j,hj,jth⟩ := List.mem_iff_getElem.mp (within a ha)
  let v : Fin basis.length := ⟨j,hj⟩
  have equal : v = u := by
    by_contra ne
    have identical := unchanged v ne
    change read (position u).1 basis[j] = read (position u).2 basis[j] at identical
    rw [jth,one,zero] at identical
    contradiction
  have same : a = w := by
    have same := congrArg (fun index : Fin basis.length => basis[index]) equal
    change basis[j] = basis[i] at same
    rwa [jth,ith] at same
  simpa [same] using ha

set_option maxHeartbeats 2400000 in
theorem minimum_of_search (excluded : search 10 basis = false) :
    IsMinimalMonoCircuit 8 witness := by
  refine ⟨mono,?_⟩
  intro C hC equal
  rw [size_eq]
  by_contra h
  have lim : C.size ≤ 10 := by omega
  have pure : ∀ g∈C.gates,g.op=.and ∨ g.op=.or := by
    intro g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hC g hg).1
  have fan : FanInTwo C := by
    intro g hg
    refine ⟨?_,(hC g hg).2⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
    rcases pure g hg with h|h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have sampled : ∀ r, C.eval (basis.map (read r)) = read r target := by
    intro r
    calc
      C.eval (basis.map (read r)) = circuitFun 8 C (assignment r) := by rw [(sample_circuit r).1]; rfl
      _ = circuitFun 8 witness (assignment r) := congrFun equal (assignment r)
      _ = read r target := (sample_circuit r).2
  obtain ⟨k, pool, cost, proof, subset⟩ := circuit_extract basis C fan pure sampled
  have reached : search 10 basis = true :=
    search_complete 10 (cost.trans lim) proof (root_eq proof subset) basis_nodup
  exact (by decide : (false : Bool) ≠ true) (excluded.symm.trans reached)

end Refute4848.Root

theorem Refute4848.exact_negation
    (minimal : PEqualNP.MetaComplexity.IsMinimalMonoCircuit 8 Refute4848.witness) : ¬ (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → PEqualNP.TopForm.NoFourCycle x2 → ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x6 → PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → ∀ x9 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x12 x13 : Fin x1), PEqualNP.EdgeOwnership.gateVal x1 x6 x9 (PEqualNP.EdgeOwnership.pairInput x12 x13) = Bool.true → x2.Adj x12 x13) := by
  intro universal
  apply Refute4848.noEdge
  exact universal 8 Refute4848.graph Refute4848.noTriangle Refute4848.noFour
    Refute4848.witness minimal Refute4848.computes 5 Refute4848.badIndex
    Refute4848.badOp 2 7 Refute4848.badInput

namespace Finite4848.Audit
structure Word where
  val : Sig
  pos : Nat
  neg : Nat
def allMarks : Nat := 2^42-1
def cover (s : Word) : Nat := s.pos &&& (allMarks ^^^ s.neg)
def coverPool (ws : List Word) : Nat := ws.foldr (fun w a=>cover w ||| a) 0
def transform (a b : Word) (op : Bool) : Word :=
  if op then ⟨a.val ||| b.val,a.pos ||| b.pos,a.neg ||| b.neg⟩
  else ⟨a.val &&& b.val,a.pos &&& b.pos,a.neg &&& b.neg⟩

def choices (rest : List Word) (a b z : Word) : List (Nat × List Word) :=
  [(0,[]),(cover a,[a]),(cover b,[b]),(cover a ||| cover b,[a,b])]

def fastStep (ws : List Word) (k : Nat) : List (List Sig) :=
  ws.flatMap fun a=>ws.flatMap fun b=>
    if a.val.toNat < b.val.toNat then
      let rest:=ws.filter (fun w=>w.val != a.val && w.val != b.val)
      let other:=coverPool rest
      [false,true].flatMap fun op=>
        let z:=transform a b op
        if ws.any (fun w=>w.val==z.val) then [] else
          let base:=other ||| cover z
          (choices rest a b z).filterMap fun (more,extra)=>
            if rest.length+extra.length+1 ≤ k+1 && base ||| more == allMarks
            then some (z.val :: (extra++rest).map Word.val)
            else none
    else []

def mask (w : Nat) := 2^w-1
def field (w packed i : Nat) := (packed>>>(w*i)) &&& mask w
def readWord (bank : Nat→Nat) (i : Nat) : Word :=
  let x:=bank i
  ⟨BitVec.ofNat 43 (x &&& mask 43),(x>>>43)&&&mask 42,(x>>>85)&&&mask 42⟩
def digits : Nat→Nat→List Nat
  | 0,_ => []
  | k+1,x => if x=0 then [] else ((x&&&1023)-1)::digits k (x>>>10)
def signals (bank records : Nat→Nat) (r : Nat) := (digits 10 (records r)).map (readWord bank)
def coversRow (bank records spans hints : Nat→Nat) (r k : Nat) : Bool :=
  let pool:=signals bank records r
  let incoming:=pool.map Word.val
  !(incoming.contains goal) && (fastStep pool k).zipIdx.all fun (next,i)=>
    let h:=hints (spans r+i)
    let out:=(signals bank records h).map Word.val
    next.isPerm out
end Finite4848.Audit

namespace Finite4848.Audit.Matrix
def laneRepeat : Nat := 0x1000000000001000000000001000000000001000000000001000000000001000000000001000000000001000000000001
def gatherMultiplier : Nat := 0x10000000000020000000000040000000000080000000000100000000000200000000000400000000000800000000001
def scatter9 (v : Nat) : Nat :=
  let y0:=(v ||| (v<<<120)) &&& 0x1000000000000000000000000000000ff
  let y1:=(y0 ||| (y0<<<60)) &&& 0x1000000000000000f000000000000000f
  let y2:=(y1 ||| (y1<<<30)) &&& 0x100000003000000030000000300000003
  let y3:=(y2 ||| (y2<<<15)) &&& 0x100010001000100010001000100010001
  y3
def gather (x : Nat) : Nat :=
  let markers:=((x + (allMarks*laneRepeat))>>>42) &&& laneRepeat
  ((markers*gatherMultiplier)>>>376) &&& 511
structure Bus where
  pos : Nat
  neg : Nat
  seen : Nat
  many : Nat
def bus : List Word→Bus
  | [] => ⟨0,0,0,0⟩
  | v::vs =>
    let tail:=bus vs
    let c:=cover v
    ⟨v.pos ||| (tail.pos<<<48),v.neg ||| (tail.neg<<<48),tail.seen ||| c,tail.many ||| (tail.seen &&& c)⟩
structure Four where
  andLeft : Nat
  andRight : Nat
  orLeft : Nat
  orRight : Nat
def blocked (critical notPos neg : Nat) : List Word→Four
  | [] => ⟨0,0,0,0⟩
  | v::vs =>
    let tail:=blocked critical notPos neg vs
    let r:=(critical &&& cover v)*laneRepeat
    let a:=gather (r &&& notPos)
    let o:=gather (r &&& neg)
    ⟨a ||| (tail.andLeft<<<16),scatter9 a ||| (tail.andRight<<<1),
      o ||| (tail.orLeft<<<16),scatter9 o ||| (tail.orRight<<<1)⟩
def triangle (n : Nat) : Nat := if n=4 then 0x8000c000e else if n=5 then 0x100018001c001e else if n=6 then 0x2000300038003c003e else if n=7 then 0x40006000700078007c007e else if n=8 then 0x8000c000e000f000f800fc00fe else if n=9 then 0x100018001c001e001f001f801fc01fe else 0
def gateOptions (n k tri left right : Nat) :=
  let yes (bad : Nat) := tri ^^^ (tri &&& bad)
  (if n ≤ k then tri else 0) |||
  ((if n ≤ k+1 then yes left else 0)<<<144) |||
  ((if n ≤ k+1 then yes right else 0)<<<288) |||
  ((if n ≤ k+2 then yes (left ||| right) else 0)<<<432)
def candidates (ws : List Word) (k : Nat) : Nat :=
  let bs:=bus ws
  let vs:=blocked (bs.seen ^^^ bs.many) (allMarks*laneRepeat ^^^ bs.pos) bs.neg ws
  let t:=triangle ws.length
  gateOptions ws.length k t vs.andLeft vs.andRight ||| (gateOptions ws.length k t vs.orLeft vs.orRight<<<576)
end Finite4848.Audit.Matrix

namespace Finite4848.Audit.Simple
def packRow {α : Type} (f : α→Bool) : List α→Nat
  | []=>0
  | x::xs=>(if f x then 1 else 0) ||| (packRow f xs<<<1)
def stack (f : Word→Nat) : List Word→Nat
  | []=>0
  | x::xs=>f x ||| (stack f xs<<<16)
def grid (xs : List Word) (f : Word→Word→Bool) : Nat := stack (fun a=>packRow (f a) xs) xs
def andBad (unique : Nat) (a b : Word) := (unique &&& cover a &&& (allMarks ^^^ b.pos))!=0
def orBad (unique : Nat) (a b : Word) := (unique &&& cover a &&& b.neg)!=0
def candidates (xs : List Word) (k : Nat) : Nat :=
  let v:=Matrix.bus xs
  let c:=v.seen ^^^ v.many
  let t:=Matrix.triangle xs.length
  let a:=grid xs (andBad c)
  let b:=grid xs (fun x y=>andBad c y x)
  let o:=grid xs (orBad c)
  let p:=grid xs (fun x y=>orBad c y x)
  Matrix.gateOptions xs.length k t a b ||| (Matrix.gateOptions xs.length k t o p<<<576)
end Finite4848.Audit.Simple

namespace Finite4848.Audit
theorem missingPerm {xs ys : List Sig} (h : xs.Perm ys) (p : Nat) :
    missing p xs=missing p ys := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [missing,ih]
  | swap a b l =>
    by_cases ha : a.getLsbD p=true <;> by_cases hb : b.getLsbD p=true <;>
      simp [missing,ha,hb,← BitVec.and_assoc,BitVec.and_comm b a]
  | trans h₁ h₂ i₁ i₂ => exact i₁.trans i₂

theorem separatesPerm {xs ys : List Sig} (h : xs.Perm ys) : canSeparate xs=canSeparate ys := by
  simp only [canSeparate,missingPerm h]

theorem nextPerm {xs ys : List Sig} (h : xs.Perm ys) {a b z : Sig} {t : List Sig}
    (mem : t∈nextPools xs a b z) : ∃ u∈nextPools ys a b z, t.Perm u := by
  let f : Sig→Bool := fun w=>w != a && w != b
  have hr := h.filter f
  change t ∈ [z :: xs.filter f, z :: a :: xs.filter f, z :: b :: xs.filter f, z :: a :: b :: xs.filter f] at mem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl
  · exact ⟨_,by simp [nextPools,f],hr.cons z⟩
  · exact ⟨_,by simp [nextPools,f],(hr.cons a).cons z⟩
  · exact ⟨_,by simp [nextPools,f],(hr.cons b).cons z⟩
  · exact ⟨_,by simp [nextPools,f],((hr.cons b).cons a).cons z⟩

theorem successorPerm {xs ys : List Sig} (h : xs.Perm ys) {t : List Sig} {k : Nat}
    (mem : t∈successors xs k) : ∃ u∈successors ys k, t.Perm u := by
  unfold successors at mem ⊢
  obtain ⟨a,ha,inner⟩ := List.mem_flatMap.mp mem
  obtain ⟨b,hb,choice⟩ := List.mem_flatMap.mp inner
  split at choice
  next lt =>
    obtain ⟨z,hz,child⟩ := List.mem_flatMap.mp choice
    by_cases seen : xs.contains z=true
    · simp only [seen,if_true,List.not_mem_nil] at child
    · have zs : xs.contains z=false := Bool.eq_false_iff.mpr seen
      have zy : ys.contains z=false := by
        apply Bool.eq_false_iff.mpr
        intro e
        exact seen (List.contains_iff_mem.mpr (h.mem_iff.mpr (List.contains_iff_mem.mp e)))
      simp only [zs,Bool.false_eq_true,if_false] at child
      obtain ⟨hm,good⟩ := List.mem_filter.mp child
      obtain ⟨u,hu,per⟩ := nextPerm h hm
      refine ⟨u,List.mem_flatMap.mpr ⟨a,h.mem_iff.mp ha,List.mem_flatMap.mpr ⟨b,h.mem_iff.mp hb,?_⟩⟩,per⟩
      simp only [lt,if_true]
      apply List.mem_flatMap.mpr
      refine ⟨z,hz,?_⟩
      simp only [zy,Bool.false_eq_true,if_false]
      apply List.mem_filter.mpr
      exact ⟨hu,by simpa only [← per.length_eq,← separatesPerm per] using good⟩
  next => simp at choice

theorem searchTruePerm (k : Nat) {xs ys : List Sig} (h : xs.Perm ys) :
    search k xs=true → search k ys=true := by
  induction k generalizing xs ys with
  | zero => simpa only [search,List.contains_iff_mem] using h.mem_iff.mp
  | succ k ih =>
    intro hx
    rcases Bool.or_eq_true_iff.mp hx with present|more
    · exact Bool.or_eq_true_iff.mpr (.inl (List.contains_iff_mem.mpr (h.mem_iff.mp (List.contains_iff_mem.mp present))))
    · obtain ⟨t,ht,hit⟩:=List.any_eq_true.mp more
      obtain ⟨u,hu,per⟩:=successorPerm h ht
      exact Bool.or_eq_true_iff.mpr (.inr (List.any_eq_true.mpr ⟨u,hu,ih per hit⟩))
theorem searchPerm (k : Nat) {xs ys : List Sig} (h : xs.Perm ys) : search k xs=search k ys := by
  apply Bool.eq_iff_iff.mpr
  exact ⟨searchTruePerm k h,searchTruePerm k h.symm⟩
end Finite4848.Audit

namespace Finite4848.Audit

def separates (p n : Nat) (w : Sig) : Bool := w.getLsbD p && !w.getLsbD n

theorem missing_false {p n : Nat} (bound : n < 43) (pool : List Sig)
    (h : (missing p pool).getLsbD n=false) : ∃ w∈pool, separates p n w=true := by
  induction pool with
  | nil =>
    change (BitVec.allOnes 43).getLsbD n=false at h
    rw [BitVec.getLsbD_allOnes,decide_eq_true bound] at h
    contradiction
  | cons x xs ih =>
    by_cases hp : x.getLsbD p=true
    · simp only [missing,hp,ite_true,BitVec.getLsbD_and] at h
      by_cases hn : x.getLsbD n=true
      · obtain ⟨w,hw,good⟩ := ih (by simpa only [hn,Bool.true_and] using h)
        exact ⟨w,List.mem_cons_of_mem x hw,good⟩
      · exact ⟨x,List.mem_cons_self,by simp [separates,hp,hn]⟩
    · obtain ⟨w,hw,good⟩ := ih (by simpa [missing,hp] using h)
      exact ⟨w,List.mem_cons_of_mem x hw,good⟩

theorem pairNecessary {p n : Nat} {pool : List Sig} (pos : p < 8) (neg : n < 43)
    (nTarget : goal.getLsbD n=false) (ok : canSeparate pool=true) :
    ∃ w ∈ pool,separates p n w=true := by
  have bit := List.all_eq_true.mp ok p (List.mem_range.mpr pos)
  have eq : missing p pool &&& ~~~goal=0 := beq_iff_eq.mp bit
  have h := congrArg (fun w : Sig=>w.getLsbD n) eq
  apply missing_false neg
  change (missing p pool &&& ~~~goal).getLsbD n=(0 : Sig).getLsbD n at h
  have zero : (0 : Sig).getLsbD n=false := by change (0 : Nat).testBit n=false; simp
  simpa only [BitVec.getLsbD_and,BitVec.getLsbD_not,decide_eq_true neg,nTarget,Bool.not_false,Bool.true_and,Bool.and_true,zero] using h

theorem closesLayer {xs : List Sig} {k : Nat} {next : List (List Sig)}
    (stop : xs.contains goal=false)
    (allNext : ∀ c∈successors xs k, ∃ u∈next,c.Perm u)
    (exclude : ∀ u∈next,search k u=false) : search (k+1) xs=false := by
  apply Bool.eq_false_iff.mpr
  intro hit
  rcases Bool.or_eq_true_iff.mp hit with done|tail
  · change xs.contains goal=true at done
    rw [stop] at done
    contradiction
  · obtain ⟨w,hm,hy⟩ := List.any_eq_true.mp tail
    obtain ⟨u,hu,perm⟩ := allNext w hm
    rw [searchPerm k perm,exclude u hu] at hy
    contradiction

end Finite4848.Audit

namespace Finite4848.Audit.Simple

theorem bitHead (b : Bool) : (if b then 1 else 0 : Nat).testBit 0=b := by cases b <;> decide
theorem bitTail (b : Bool) (j : Nat) : (if b then 1 else 0 : Nat).testBit (j+1)=false := by
  cases b
  · simp
  · apply Bool.eq_false_iff.mpr
    simp [Nat.testBit_one_eq_true_iff_self_eq_zero]

theorem pack_at {α : Type} (f : α→Bool) (xs : List α) (j : Nat) (x : α)
    (h : xs[j]?=some x) : (packRow f xs).testBit j=f x := by
  induction xs generalizing j with
  | nil => simp at h
  | cons a xs ih =>
    cases j with
    | zero => simp at h; subst x; cases hfa : f a <;> simp [packRow,hfa]
    | succ j =>
      have h' : xs[j]?=some x := by simpa using h
      simp [packRow,bitTail,ih _ h']

theorem pack_off {α : Type} (f : α→Bool) (xs : List α) (j : Nat) (h : xs.length ≤ j) :
    (packRow f xs).testBit j=false := by
  induction xs generalizing j with
  | nil => simp [packRow]
  | cons a xs ih =>
    cases j with
    | zero => simp at h
    | succ j =>
      have h' : xs.length ≤ j := by simpa using h
      simp [packRow,bitTail,ih _ h']

theorem stack_at (xs : List Word) (f : Word→Nat)
    (off : ∀ x∈xs,∀ j,16 ≤ j → (f x).testBit j=false) (i j : Nat) (w : Word)
    (row : xs[i]?=some w) (hj : j < 16) : (stack f xs).testBit (16*i+j)=(f w).testBit j := by
  induction xs generalizing i with
  | nil => simp at row
  | cons a xs ih =>
    cases i with
    | zero =>
      simp at row; subst w
      simp [stack,show ¬ j≥16 by omega]
    | succ i =>
      have tail : xs[i]?=some w := by simpa using row
      have roof : 16 ≤ 16*(i+1)+j := by omega
      simp only [stack,Nat.testBit_or,Nat.testBit_shiftLeft,off a List.mem_cons_self _ roof,
        decide_eq_true roof,Bool.true_and,Bool.false_or,show 16*(i+1)+j-16=16*i+j by omega]
      exact ih (fun x hx=>off x (List.mem_cons_of_mem a hx)) i tail

theorem grid_at (xs : List Word) (f : Word→Word→Bool) (hs : xs.length ≤ 9) (i j : Nat)
    (x y : Word) (hx : xs[i]?=some x) (hy : xs[j]?=some y) : (grid xs f).testBit (16*i+j)=f x y := by
  have bound : j < xs.length := List.getElem?_eq_some_iff.mp hy |>.1
  unfold grid
  rw [stack_at _ _ (fun _ _ t ht=>pack_off _ _ _ (by omega)) _ _ _ hx (by omega)]
  exact pack_at _ _ _ _ hy

theorem seen_of_mark {w : Word} (ws : List Word) {j : Nat} (hw : w∈ws) (hc : (cover w).testBit j=true) :
    (Matrix.bus ws).seen.testBit j=true := by
  induction ws with
  | nil => simp at hw
  | cons b bs ih =>
    change ((Matrix.bus bs).seen ||| cover b).testBit j=true
    rw [Nat.testBit_or]
    rcases List.mem_cons.mp hw with rfl|later
    · simp [hc]
    · simp [ih later]

theorem many_of_two {w v : Word} (ws : List Word) {j : Nat} (hw : w∈ws) (hv : v∈ws) (dif : w.val≠v.val)
    (cw : (cover w).testBit j=true) (cv : (cover v).testBit j=true) :
    (Matrix.bus ws).many.testBit j=true := by
  induction ws with
  | nil => simp at hw
  | cons b bs ih =>
    change ((Matrix.bus bs).many ||| ((Matrix.bus bs).seen &&& cover b)).testBit j=true
    rw [Nat.testBit_or,Nat.testBit_and]
    rcases List.mem_cons.mp hw with rfl|inW <;> rcases List.mem_cons.mp hv with rfl|inV
    · contradiction
    · simp [seen_of_mark bs inV cv,cw]
    · simp [seen_of_mark bs inW cw,cv]
    · simp [ih inW inV]

theorem triangle_at : ∀ n:Fin 10,∀ i j:Fin 9,4 ≤ n.val → i.val < j.val → j.val < n.val →
  (Matrix.triangle n.val).testBit (16*i.val+j.val)=true := by decide +kernel

end Finite4848.Audit.Simple

namespace Finite4848.Audit.Simple

structure Meaning (xs : List Word) (p n : Nat→Nat) : Prop where
  pair : ∀ t, t < 42 → p t < 8 ∧ n t < 43 ∧ goal.getLsbD (n t)=false
  positive : ∀ w∈xs,∀ t,w.pos.testBit t=(decide (t < 42) && w.val.getLsbD (p t))
  negative : ∀ w∈xs,∀ t,w.neg.testBit t=(decide (t < 42) && w.val.getLsbD (n t))

theorem cover_mark {xs : List Word} {p n : Nat→Nat} (m : Meaning xs p n) {a : Word} (ha : a∈xs) (t : Nat) :
    (cover a).testBit t = (decide (t < 42) && separates (p t) (n t) a.val) := by
  simp only [cover,allMarks,Nat.testBit_and,Nat.testBit_xor,Nat.testBit_two_pow_sub_one,
    m.positive a ha t,m.negative a ha t,separates]
  cases decide (t < 42) <;> cases a.val.getLsbD (p t) <;> cases a.val.getLsbD (n t) <;> rfl

theorem forced {xs : List Word} {p n : Nat→Nat} (m : Meaning xs p n) {a : Word} (ha : a∈xs)
    {t : Nat} (hc : (cover a).testBit t=true)
    (hu : ((Matrix.bus xs).seen ^^^ (Matrix.bus xs).many).testBit t=true)
    {child : List Sig} {z : Sig} (sep : canSeparate child=true)
    (newonly : ∀ w∈child, w=z ∨ (w∈xs.map Word.val ∧ w≠a.val)) :
    separates (p t) (n t) z=true := by
  have c := hc
  rw [cover_mark m ha] at c
  obtain ⟨lt,_⟩ := Bool.and_eq_true_iff.mp c
  have hl := of_decide_eq_true lt
  obtain ⟨p8,n43,zero⟩ := m.pair t hl
  obtain ⟨w,hw,s⟩ := pairNecessary p8 n43 zero sep
  rcases newonly w hw with rfl|⟨old,ne⟩
  · exact s
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp old
    have cv : (cover v).testBit t=true := by rw [cover_mark m hv,lt,s]; rfl
    have multi := many_of_two xs ha hv (Ne.symm ne) hc cv
    rw [Nat.testBit_xor,seen_of_mark xs ha hc,multi] at hu
    contradiction

theorem and_clear {xs : List Word} {p n : Nat→Nat} (m : Meaning xs p n) {a b : Word} (ha : a∈xs) (hb : b∈xs)
    {child : List Sig} (sep : canSeparate child=true)
    (newonly : ∀ w∈child, w=a.val &&& b.val ∨ (w∈xs.map Word.val ∧ w≠a.val)) :
    andBad ((Matrix.bus xs).seen ^^^ (Matrix.bus xs).many) a b=false := by
  unfold andBad
  suffices h : ((Matrix.bus xs).seen ^^^ (Matrix.bus xs).many) &&& cover a &&& (allMarks ^^^ b.pos)=0 by simp [h]
  apply Nat.eq_of_testBit_eq
  intro t
  simp only [Nat.zero_testBit]
  apply Bool.eq_false_iff.mpr
  intro bad
  simp only [Nat.testBit_and,Bool.and_eq_true] at bad
  obtain ⟨⟨u,c⟩,bneg⟩:=bad
  have cross:=forced m ha c u sep newonly
  have pos := (Bool.and_eq_true_iff.mp cross).1
  rw [BitVec.getLsbD_and,Bool.and_eq_true] at pos
  have inside:=((Bool.and_eq_true_iff.mp ((cover_mark m ha t).symm.trans c))).1
  rw [Nat.testBit_xor,allMarks,Nat.testBit_two_pow_sub_one,m.positive b hb,inside,pos.2] at bneg
  contradiction

theorem or_clear {xs : List Word} {p n : Nat→Nat} (m : Meaning xs p n) {a b : Word} (ha : a∈xs) (hb : b∈xs)
    {child : List Sig} (sep : canSeparate child=true)
    (newonly : ∀ w∈child, w=a.val ||| b.val ∨ (w∈xs.map Word.val ∧ w≠a.val)) :
    orBad ((Matrix.bus xs).seen ^^^ (Matrix.bus xs).many) a b=false := by
  unfold orBad
  suffices h : ((Matrix.bus xs).seen ^^^ (Matrix.bus xs).many) &&& cover a &&& b.neg=0 by simp [h]
  apply Nat.eq_of_testBit_eq
  intro t
  simp only [Nat.zero_testBit]
  apply Bool.eq_false_iff.mpr
  intro bad
  simp only [Nat.testBit_and,Bool.and_eq_true] at bad
  obtain ⟨⟨u,c⟩,bp⟩:=bad
  have cross:=forced m ha c u sep newonly
  have no := (Bool.and_eq_true_iff.mp cross).2
  change !(a.val ||| b.val).getLsbD (n t)=true at no
  rw [BitVec.getLsbD_or] at no
  rw [m.negative b hb] at bp
  have btrue := (Bool.and_eq_true_iff.mp bp).2
  simp [btrue] at no

end Finite4848.Audit.Simple

namespace Finite4848.Audit.Simple

def mode (x y : Bool) : Nat := x.toNat+2*y.toNat

theorem option_bit (n k tri left right s : Nat) (da db : Bool)
    (t : tri.testBit s=true) (hlen : n ≤ k+da.toNat+db.toNat)
    (la : da=true → left.testBit s=false) (rb : db=true → right.testBit s=false) :
    (Matrix.gateOptions n k tri left right).testBit (s+144*mode da db)=true := by
  have diff (a : Nat) : s+a-a=s := by omega
  have inside (a : Nat) : a ≤ s+a := by omega
  cases da <;> cases db <;>
    simp [mode,Bool.toNat] at hlen la rb ⊢ <;>
    simp [Matrix.gateOptions,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_xor,Nat.testBit_and,
        diff,inside,hlen,t,la,rb,Nat.add_assoc] <;> omega

def gateWord (op : Bool) (a b : Sig) : Sig := if op then a ||| b else a &&& b
def kept (da db : Bool) (a b : Sig) : List Sig :=
  (if da then [] else [a]) ++ (if db then [] else [b])
def discard (xs : List Sig) (a b : Sig) := xs.filter (fun w=> w != a && w != b)
def chosen (ws : List Sig) (a b : Sig) (op da db : Bool) :=
  gateWord op a b :: (kept da db a b ++ discard ws a b)

theorem chosen_shape {ws : List Sig} {a b : Sig} (ha : a∈ws) (hb : b∈ws) (ne : a≠b)
    (op da db : Bool) : (∀ w∈chosen ws a b op da db, w=gateWord op a b ∨ w∈ws ∧ (da=true → w≠a) ∧ (db=true → w≠b)) := by
  intro w hw
  rcases List.mem_cons.mp hw with top|rest
  · exact Or.inl top
  right
  rcases List.mem_append.mp rest with inputs|tail
  · cases da <;> cases db <;> simp [kept] at inputs <;> first
      | rcases inputs with rfl|rfl <;> simp [ha,hb,ne,Ne.symm ne]
      | subst w; simp [ha,hb,ne,Ne.symm ne]
  · obtain ⟨mem,h⟩:=List.mem_filter.mp tail
    simpa using And.intro mem (And.intro (fun (_ : da=true) => (by simpa using (Bool.and_eq_true_iff.mp h).1 : w≠a))
      (fun (_ : db=true) => (by simpa using (Bool.and_eq_true_iff.mp h).2 : w≠b)))

theorem chosen_length {ws:List Sig} {a b:Sig} (h : (discard ws a b).length+2=ws.length)
    (op da db : Bool) :
    (chosen ws a b op da db).length+da.toNat+db.toNat=ws.length+1 := by
  cases da <;> cases db <;> simp [chosen,kept,Bool.toNat] <;> omega

theorem candidate_bit {xs : List Word} {p n : Nat→Nat} (m : Meaning xs p n)
    {i j : Nat} {a b : Word} (ai : xs[i]?=some a) (bj : xs[j]?=some b)
    (lt : i < j) (sm : 4 ≤ xs.length) (bg : xs.length ≤ 9) (ne : a.val≠b.val)
    (op da db : Bool) {k : Nat}
    (len : xs.length ≤ k+da.toNat+db.toNat)
    (sep : canSeparate (chosen (xs.map Word.val) a.val b.val op da db)=true) :
    (candidates xs k).testBit (16*i+j+144*mode da db+576*op.toNat)=true := by
  obtain ⟨ai',_⟩:=List.getElem?_eq_some_iff.mp ai
  obtain ⟨bj',_⟩:=List.getElem?_eq_some_iff.mp bj
  have ha : a∈xs := List.mem_iff_getElem?.mpr ⟨i,ai⟩
  have hb : b∈xs := List.mem_iff_getElem?.mpr ⟨j,bj⟩
  have am : a.val∈xs.map Word.val := List.mem_map.mpr ⟨a,ha,rfl⟩
  have bm : b.val∈xs.map Word.val := List.mem_map.mpr ⟨b,hb,rfl⟩
  have parts:=chosen_shape am bm ne op da db
  have t := triangle_at ⟨xs.length,by omega⟩ ⟨i,by omega⟩ ⟨j,by omega⟩ sm lt bj'
  cases op
  · have l (d : da=true) := and_clear m ha hb sep (fun w hw=>(parts w hw).imp_right (fun h=>⟨h.1,h.2.1 d⟩))
    have r (d : db=true) := and_clear m hb ha sep (fun w hw=>(parts w hw).imp
      (fun eq=>by simpa [gateWord,BitVec.and_comm] using eq) (fun h=>⟨h.1,h.2.2 d⟩))
    unfold candidates
    rw [Nat.testBit_or]
    simp only [Bool.toNat_false,Nat.mul_zero,Nat.add_zero]
    apply Bool.or_eq_true_iff.mpr
    left
    apply option_bit _ _ _ _ _ _ da db t len
    · intro d; rw [grid_at _ _ bg i j a b ai bj]; exact l d
    · intro d; rw [grid_at _ _ bg i j a b ai bj]; exact r d
  · have l (d : da=true) := or_clear m ha hb sep (fun w hw=>(parts w hw).imp_right (fun h=>⟨h.1,h.2.1 d⟩))
    have r (d : db=true) := or_clear m hb ha sep (fun w hw=>(parts w hw).imp
      (fun eq=>by simpa [gateWord,BitVec.or_comm] using eq) (fun h=>⟨h.1,h.2.2 d⟩))
    unfold candidates
    rw [Nat.testBit_or]
    apply Bool.or_eq_true_iff.mpr
    right
    rw [Nat.testBit_shiftLeft]
    simp only [Bool.toNat_true,Nat.mul_one,show 576 ≤ 16*i+j+144*mode da db+576 by omega,decide_true,
      Bool.true_and,show 16*i+j+144*mode da db+576-576=16*i+j+144*mode da db by omega]
    apply option_bit _ _ _ _ _ _ da db t len
    · intro d; rw [grid_at _ _ bg i j a b ai bj]; exact l d
    · intro d; rw [grid_at _ _ bg i j a b ai bj]; exact r d
end Finite4848.Audit.Simple

namespace Finite4848.Audit.Simple
def Increasing (ws : List Sig) := ws.Pairwise fun a b=>a.toNat < b.toNat

theorem increasing_nodup {xs : List Sig} (hi : Increasing xs) : xs.Nodup := by
  apply List.Pairwise.imp _ hi
  intro a b lt eq
  subst b
  exact Nat.lt_irrefl _ lt

theorem filter_one (a : Sig) (xs : List Sig) (nd : xs.Nodup) :
    (xs.filter (fun w=>w != a)).length + (if a∈xs then 1 else 0)=xs.length := by
  induction xs with
  | nil => simp
  | cons b bs ih =>
    obtain ⟨outside,rest⟩ := List.nodup_cons.mp nd
    have h := ih rest
    by_cases same : b=a
    · subst b; simp [outside] at h ⊢; omega
    · by_cases mem : a∈bs
      · simp [same,Ne.symm same,mem] at h ⊢; omega
      · simp [same,Ne.symm same,mem] at h ⊢; omega

theorem discard_length {xs : List Sig} {a b : Sig} (hi : Increasing xs) (ha : a∈xs) (hb : b∈xs) (ab : a≠b) :
    (discard xs a b).length+2=xs.length := by
  have nd:=increasing_nodup hi
  let rest:=xs.filter (fun w=>w != b)
  have ar : a∈rest := by simp [rest,ha,ab]
  have nr : rest.Nodup := nd.filter _
  have first:=filter_one b xs nd
  have second:=filter_one a rest nr
  simp only [hb,ar,ite_true] at first second
  have eqf : discard xs a b=rest.filter (fun w=>w != a) := by simp [rest,discard,List.filter_filter]
  change rest.length+1=xs.length at first
  change (rest.filter (fun w=>w != a)).length+1=rest.length at second
  rw [eqf]; omega

theorem increasing_slots {xs : List Word} (order : Increasing (xs.map Word.val)) {a b : Word}
    {i j : Nat} (qa : xs[i]?=some a) (qb : xs[j]?=some b)
    (lt : a.val.toNat < b.val.toNat) : i < j := by
  obtain ⟨hi,ea⟩:=List.getElem?_eq_some_iff.mp qa
  obtain ⟨hj,eb⟩:=List.getElem?_eq_some_iff.mp qb
  by_cases eq : i=j
  · subst j; have same : a=b := Option.some.inj (qa.symm.trans qb); exact False.elim ((Nat.lt_irrefl _) (same ▸ lt))
  by_cases rev : j < i
  · have v:=List.pairwise_iff_getElem.mp order j i (by simpa using hj) (by simpa using hi) rev
    simp only [List.getElem_map,ea,eb] at v; omega
  · omega

theorem next_chosen {xs : List Sig} {a b : Sig} (op : Bool) {w : List Sig}
    (hw : w∈nextPools xs a b (gateWord op a b)) : ∃ da db : Bool,w=chosen xs a b op da db := by
  change w∈[_,_,_,_] at hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with h|h|h|h
  · exact ⟨true,true,h⟩
  · exact ⟨false,true,h⟩
  · exact ⟨true,false,h⟩
  · exact ⟨false,false,h⟩

theorem explain {xs : List Sig} {k : Nat} {w : List Sig} (h : w∈successors xs k) :
    ∃ a∈xs,∃ b∈xs,a.toNat < b.toNat ∧ ∃ op da db : Bool,
       xs.contains (gateWord op a b)=false ∧ w=chosen xs a b op da db ∧ w.length ≤ k+1 ∧ canSeparate w=true := by
  unfold successors at h
  obtain ⟨a,ha,s⟩ := List.mem_flatMap.mp h
  obtain ⟨b,hb,choice⟩ := List.mem_flatMap.mp s
  split at choice
  next lt =>
    obtain ⟨z,zs,children⟩:=List.mem_flatMap.mp choice
    split at children
    next => simp at children
    next fresh =>
      obtain ⟨nx,ok⟩:=List.mem_filter.mp children
      obtain ⟨size,can⟩:=Bool.and_eq_true_iff.mp ok
      have cook (op : Bool) (r : z=gateWord op a b) :
          ∃ op da db : Bool,xs.contains (gateWord op a b)=false ∧ w=chosen xs a b op da db ∧ w.length ≤ k+1 ∧ canSeparate w=true := by
        subst z
        obtain ⟨da,db,eq⟩:=next_chosen op nx
        exact ⟨op,da,db,Bool.eq_false_iff.mpr fresh,eq,of_decide_eq_true size,can⟩
      refine ⟨a,ha,b,hb,lt,?_⟩
      simp only [List.mem_cons,List.not_mem_nil,or_false] at zs
      rcases zs with eq|eq
      · exact cook false eq
      · exact cook true eq
  next => simp at choice

end Finite4848.Audit.Simple

namespace Finite4848.Audit.Matrix
structure Certificate where
  bank : Nat→Nat
  states : Nat→Nat
  offsets : Nat→Nat
  edges : Nat→Nat

def values (c : Certificate) (r : Nat) : List Sig := (signals c.bank c.states r).map Word.val

def edgeOK (c : Certificate) (ws : List Sig) (lo hi stamp target : Nat) : Bool :=
  let code:=stamp % 144
  let a := ws.getD (code/16) 0
  let b := ws.getD (code % 16) 0
  let flavor:=stamp/144
  let z:=if flavor/4=1 then a ||| b else a &&& b
  if target ≥ 8192 then ws[target-8192]? == some z
  else
    let rest:=ws.filter (fun w=> w != a && w != b)
    let mode:=flavor % 4
    let expected:=z :: ((if mode.testBit 0 then [] else [a]) ++ (if mode.testBit 1 then [] else [b]) ++ rest)
    (lo ≤ target) && (target < hi) && expected.isPerm (values c target)

def reported (c : Certificate) (start : Nat) (n : Nat) : Nat :=
  (List.range n).foldr (fun i so=>so ||| (1<<<((c.edges (start+i))&&&2047))) 0

def checkRow (c : Certificate) (k lo hi r : Nat) : Bool :=
  let ws:=signals c.bank c.states r
  let s:=c.offsets r
  let n:=c.offsets (r+1)-s
  let possible:=candidates ws k
  let available:=reported c s n
  let xs:=ws.map Word.val
  !(xs.contains goal) && (4 ≤ ws.length) && (ws.length ≤ 9) &&
    (possible &&& available == possible) &&
    (List.range n).all fun j=>
      let e:=c.edges (s+j)
      edgeOK c xs lo hi (e&&&2047) (e>>>11)
end Finite4848.Audit.Matrix

namespace Finite4848.Audit.Simple
def check (c : Matrix.Certificate) (k lo hi r : Nat) : Bool :=
  let ws:=signals c.bank c.states r
  let s:=c.offsets r
  let n:=c.offsets (r+1)-s
  let possible:=candidates ws k
  let available:=Matrix.reported c s n
  let xs:=ws.map Word.val
  (!(xs.contains goal) && decide (xs.Pairwise (fun a b=>a.toNat < b.toNat))) &&
    ((4 ≤ ws.length) && (ws.length ≤ 9)) &&
    (possible &&& available == possible) &&
    (List.range n).all fun j=>
      let e:=c.edges (s+j)
      Matrix.edgeOK c xs lo hi (e&&&2047) (e>>>11)
end Finite4848.Audit.Simple

namespace Finite4848.Audit.Simple
theorem oneShift {b j : Nat} (h : (1<<<j : Nat).testBit b=true) : j=b := by
  rw [Nat.testBit_shiftLeft] at h
  obtain ⟨bound,bit⟩:=Bool.and_eq_true_iff.mp h
  have zero:=Nat.testBit_one_eq_true_iff_self_eq_zero.mp bit
  have le:=of_decide_eq_true bound
  omega

theorem reportAt (c : Matrix.Certificate) (start n b : Nat)
    (h : (Matrix.reported c start n).testBit b=true) :
    ∃ j < n, (c.edges (start+j) &&& 2047)=b := by
  let e:=fun j : Nat => c.edges (start+j) &&& 2047
  have go (xs : List Nat) : (xs.foldr (fun j v=>v ||| (1<<<e j)) 0).testBit b=true → ∃ j∈xs,e j=b := by
    induction xs with
    | nil => simp
    | cons j xs ih =>
      intro yes
      rw [List.foldr_cons,Nat.testBit_or] at yes
      rcases Bool.or_eq_true_iff.mp yes with old|new
      · obtain ⟨l,mem,eq⟩:=ih old
        exact ⟨l,List.mem_cons_of_mem j mem,eq⟩
      · exact ⟨j,List.mem_cons_self,oneShift new⟩
  obtain ⟨j,hj,e⟩:=go (List.range n) h
  exact ⟨j,List.mem_range.mp hj,e⟩

theorem coversBit {m v t : Nat} (h : m &&& v=m) (bit : m.testBit t=true) : v.testBit t=true := by
  have hh:=congrArg (fun u : Nat=>u.testBit t) h
  change (m &&& v).testBit t=m.testBit t at hh
  simpa [bit] using hh
end Finite4848.Audit.Simple

namespace Finite4848.Audit.Simple
open Matrix

theorem stamp_small {i j : Nat} (hi : i < 9) (hj : j < 9) (op da db : Bool) :
    16*i+j+144*mode da db+576*op.toNat < 2048 := by
  cases op <;> cases da <;> cases db <;> simp [mode,Bool.toNat] <;> omega

theorem stamp_checked {c : Certificate} {ws : List Sig} {lo top i j target : Nat}
    {a b : Sig} (ha : ws[i]? = some a) (hb : ws[j]? = some b)
    (hi : i < 9) (hj : j < 9) (op da db : Bool)
    (newWord : gateWord op a b ∉ ws)
    (checked : edgeOK c ws lo top (16*i+j+144*mode da db+576*op.toNat) target = true) :
    lo ≤ target ∧ target < top ∧ (chosen ws a b op da db).Perm (values c target) := by
  let stamp := 16*i+j+144*mode da db+576*op.toNat
  change edgeOK c ws lo top stamp target = true at checked
  have code : stamp % 144 = 16*i+j := by
    cases op <;> cases da <;> cases db <;> simp [stamp,mode,Bool.toNat] <;> omega
  have ix : (stamp % 144) / 16 = i := by omega
  have jx : (stamp % 144) % 16 = j := by omega
  have flavor : stamp / 144 = mode da db + 4*op.toNat := by
    cases op <;> cases da <;> cases db <;> simp [stamp,mode,Bool.toNat] <;> omega
  have flag : (stamp / 144) / 4 = op.toNat := by
    rw [flavor]
    cases op <;> cases da <;> cases db <;> decide
  have keep0 : ((stamp/144)%4).testBit 0 = da := by
    rw [flavor]
    cases op <;> cases da <;> cases db <;> decide
  have keep1 : ((stamp/144)%4).testBit 1 = db := by
    rw [flavor]
    cases op <;> cases da <;> cases db <;> decide
  have gate : (if (stamp/144)/4=1 then a ||| b else a &&& b) = gateWord op a b := by
    rw [flag]
    cases op <;> rfl
  have getA : ws.getD ((stamp % 144)/16) 0 = a := by
    rw [ix,List.getD_eq_getElem?_getD,ha]; rfl
  have getB : ws.getD ((stamp % 144)%16) 0 = b := by
    rw [jx,List.getD_eq_getElem?_getD,hb]; rfl
  unfold edgeOK at checked
  simp only [getA,getB,gate,keep0,keep1] at checked
  by_cases marker : 8192 ≤ target
  · simp only [marker,ite_true,beq_iff_eq] at checked
    exact (newWord (List.mem_of_getElem? checked)).elim
  · simp only [marker,ite_false] at checked
    have chosenOK : ((lo ≤ target) && (target < top) &&
        (chosen ws a b op da db).isPerm (values c target)) = true := by
      simpa only [chosen,kept,discard] using checked
    obtain ⟨bounds,per⟩ := Bool.and_eq_true_iff.mp chosenOK
    obtain ⟨low,high⟩ := Bool.and_eq_true_iff.mp bounds
    exact ⟨of_decide_eq_true low,of_decide_eq_true high,List.isPerm_iff.mp per⟩

end Finite4848.Audit.Simple

namespace Finite4848.Audit.Simple
open Matrix

theorem proper_transition {c : Certificate} {r k lo hi : Nat} {p n : Nat→Nat}
    (meaning : Meaning (signals c.bank c.states r) p n)
    (ok : check c k lo hi r=true) {child : List Sig} (move : child∈successors (values c r) k) :
    ∃ q, lo ≤ q ∧ q < hi ∧ child.Perm (values c q) := by
  let xs:=signals c.bank c.states r
  let ws:=xs.map Word.val
  let start:=c.offsets r
  let count:=c.offsets (r+1)-start
  obtain ⟨first,edges⟩:=Bool.and_eq_true_iff.mp ok
  obtain ⟨structural,bitCover⟩:=Bool.and_eq_true_iff.mp first
  obtain ⟨shape,width⟩:=Bool.and_eq_true_iff.mp structural
  obtain ⟨_,ord⟩:=Bool.and_eq_true_iff.mp shape
  obtain ⟨small,big⟩:=Bool.and_eq_true_iff.mp width
  have order : ws.Pairwise (fun a b=>a.toNat < b.toNat) := of_decide_eq_true ord
  have low : 4 ≤ xs.length := of_decide_eq_true small
  have high : xs.length ≤ 9 := of_decide_eq_true big
  have bitEq : candidates xs k &&& reported c start count=candidates xs k := beq_iff_eq.mp bitCover
  obtain ⟨a,ha,b,hb,lt,op,da,db,newWord,eq,sz,sep⟩:=explain move
  have am : a∈ws := ha
  have bm : b∈ws := hb
  obtain ⟨aw,memA,eA⟩:=List.mem_map.mp am
  obtain ⟨bw,memB,eB⟩:=List.mem_map.mp bm
  subst a; subst b
  obtain ⟨i,ia⟩:=List.mem_iff_getElem?.mp memA
  obtain ⟨j,jb⟩:=List.mem_iff_getElem?.mp memB
  have ii : i < xs.length := (List.getElem?_eq_some_iff.mp ia).1
  have jj : j < xs.length := (List.getElem?_eq_some_iff.mp jb).1
  have ne : aw.val≠bw.val := by intro e; rw [e] at lt; omega
  have del := discard_length order am bm ne
  have sizing := chosen_length del op da db
  have bound : xs.length ≤ k+da.toNat+db.toNat := by
    change (chosen ws aw.val bw.val op da db).length+da.toNat+db.toNat=ws.length+1 at sizing
    rw [eq] at sz
    have ww : ws.length=xs.length := List.length_map _
    change (chosen ws aw.val bw.val op da db).length ≤ k+1 at sz
    omega
  have index:=increasing_slots order ia jb lt
  have bit:=candidate_bit meaning ia jb index low high ne op da db bound (eq ▸ sep)
  have covered:=coversBit bitEq bit
  obtain ⟨h,hh,code⟩:=reportAt c start count _ covered
  have ensure:=List.all_eq_true.mp edges h (List.mem_range.mpr hh)
  change edgeOK c ws lo hi (c.edges (start+h) &&& 2047) ((c.edges (start+h))>>>11)=true at ensure
  rw [code] at ensure
  have va : ws[i]?=some aw.val := by simp [ws,List.getElem?_map,ia]
  have vb : ws[j]?=some bw.val := by simp [ws,List.getElem?_map,jb]
  have fresh : gateWord op aw.val bw.val ∉ ws := by
    intro orig; have hit:=List.contains_iff_mem.mpr orig
    change ws.contains (gateWord op aw.val bw.val)=false at newWord
    rw [hit] at newWord
    contradiction
  obtain ⟨l,hg,per⟩:=stamp_checked va vb (by omega) (by omega) op da db fresh ensure
  exact ⟨_,l,hg,eq ▸ per⟩

theorem original_step {c : Certificate} {r k lo hi : Nat} {p n : Nat→Nat}
    (meaning : Meaning (signals c.bank c.states r) p n)
    (ok : check c k lo hi r=true)
    (next : ∀ q,lo ≤ q → q < hi → search k (values c q)=false) :
    search (k+1) (values c r)=false := by
  obtain ⟨first,_⟩:=Bool.and_eq_true_iff.mp ok
  obtain ⟨structural,_⟩:=Bool.and_eq_true_iff.mp first
  obtain ⟨shape,_⟩:=Bool.and_eq_true_iff.mp structural
  obtain ⟨no,_⟩:=Bool.and_eq_true_iff.mp shape
  apply Bool.eq_false_iff.mpr
  intro hit
  rcases Bool.or_eq_true_iff.mp hit with atRoot|afterGate
  · change (values c r).contains goal=true at atRoot
    change !((values c r).contains goal)=true at no
    rw [atRoot] at no
    contradiction
  · obtain ⟨child,hc,yes⟩:=List.any_eq_true.mp afterGate
    obtain ⟨q,l,h,per⟩:=proper_transition meaning ok hc
    rw [searchPerm k per,next q l h] at yes
    contradiction
end Finite4848.Audit.Simple

namespace Finite4848.Audit.Simple.Compact
open Matrix
def bank (i : Nat) : Nat := field 127 (if i < 336 then (if i < 160 then (if i < 80 then (if i < 32 then (if i < 16 then 0x7c03f800000000000480000000000000f8000ffe0000000008c0000000000001f0001f00000000001100000000000003e00000000000000020000000000000003fff80000000000038000000000000007f800000000000006000000000000000f0fe000000000000a000000000000001e00000000000000100000000000000003ff80000000000018000000000000000780f8000000000028000000000000000f00000000000000400000000000000001fc00000000000040000000000000000007ff00000000006000000000000000000f80000000000080000000000000000000fc000000000080000000000000000000000000000000 else 0x3ff8000003f0000000018200000000007ff00000000000000003000000000000f800f000000000000004800000000001f00000001f8000000008100000000003e00000000000000000100000000000003ff800000000000000180000000000007e0fffe000000000002e000000000000fc1e1fc0000000000054000000000001f83c00000000000000a0000000000003f0007f00000000000110000000000007e00000000000000002000000000000003ffffc000000000003c00000000000007c3fffc00000000005c0000000000000f87ff000000000000b00000000000001f0f01f00000000001500000000000003e1e000000000000028) else (if i < 48 then 0x800120610c007c000000000010840401000240c218000780000000002108040200048184300000f00000000042100404000903086000001fc00000008420040800120610c0000000000000010840001000240c2180000000000000021000002000081002000000000000000400000000008810820001e00000000000404100000110210400003c00000000008081000002204208000007f00000000101010000044084100000001f00000002020100000881082000000001f8000004040100001102104000000000000000080800000020042080000000000000001000000000000000ffe0f0fe000000000006a00000000001ffc1e00000000000000d0 else (if i < 64 then 0x800320610c0000000000000012840001000660c2180000000000000025010002000881002f80000000000000480040040011020040001e00000000009000100800220400800003c00000000120001010004408010000007f000000024000102000881002000000000fc0000480000840011020040000000000000009000000800120610c0000000000000010a40001000260c218000000000000002141000200048184307e000000000000428020040009030860001e00000000008500100800120610c00003c0000000010a00101000240c218000007f00000002140010200048184300000000000000042800004000983086000000000000000842400 else 0x40100a314000000003f000200900020080201462800000000000004012000001004028c5000000000000008020000002000041080000000000000100000000821330610fff83fff800000012a4db81042660c21fc007fff07e00002549a742084cc1843f800fffe00000004a934e041099830860ffffffc000000095267c0821330610c1f83fff800000012a4cb81042660c21800ffffff80000025498f82084cc1843001ffffe00000004a931e041099830860001ffffff8000095261f0821330610c0003ffffc0000012a4c3c1042660c2180007fff07e000025498742084cc18430000fffe00000004a930e04001903086000000000000000950000))) else (if i < 112 then (if i < 96 then 0x18a3331612c007ffff800000816a4c783146662c2580007fff00000102d49870620888500a0000000000000205800000c41090b096000000000000040a420001882021402be000000000000814001003104042805000f800000000102800080620808500a000000000fc00205000008c41010a014000000000000040a0000018820214028000000000000081000000210400200400000000000001000000002184cc38c707e0fffe00000084ad32e0430998718e0001fffc000001095a61c0840120e31c0000000000000210b00000080221462800000000000004012100001004028c507e0000000000080240200020080518a00000003e000010048002 else 0x388606144281f8000000001081800080710c0c28850000000007e02103000004e21818510a00000000000042060000018430208210000000000000840000000200404004000000000000010000000003184243c678000000000000142980000638ccc78cf07e0fffe00000284b932e0c71998f19e003ffffc000005097263c18e3331e33c0003fff800000a12e4c383184243c6780000000000001421c000063084878cf0000000000000284340000c61090f19e00000000000005086200018c2121e33c1f80000000000a10c00803184243c67800f80000000014218008063084878cf0000000000000284300000861000c118000000000000050000000) else (if i < 128 then 0x38e7371e73c0003fff800010b12a4c38718c2c3ce78000000000002162180000e3185879cf00000000000042c42800018630a0d39a00000000000085804800030c604186301f83c3f800010b00000a8618c0830c603f0000000002160000100c31810618c000000fe000042c0000021863020c31800000000000085800000038c6161e73c0000000000010a18c0000718c2c3ce78000000000002143120000e21818510a0000000000004207000001c539b8b2960fc1fffc0000840d5265c38a7371652c0003fff80001081aa4c38710c4c28850000000000002103400000e21858594b0000000000004206280001c43030a215f00000000000840c00080 else (if i < 144 then 0x2104042040000003c000001200000010420808408000000000f800240000000884101081000000000000004800000001863020c319ffc0000000008780000c030c60418630000003f800010f0000008618c0830c600000000000021e0000000e21818510a0000000000004306000001c43030a214000000000000860a0000038a7371652c0003fff800010c12a4c38710c4c28850000000000002182400000c218104108f8000000000043000004018430208210000001fc000086000000430860410420000000003f010c0000002610c0820840000000000002180000000e31818718e00000000000042c6000001c739b8f39e0fc1fffc000085895265c else 0x39c6163e73c1f8003f800012b18f8088738c2c7ce783f00000ffe025631f010ce71858f9cf07e00001f0004ac63e0211ce30b1f39e0fc000001f80958c7c04139c6163e73c1f80000000012b18f8080638c0870c603f0000000002560000100c71810e18c00000ffe00004ac00000618e3021c31800000000000095800000039c6163e73c0000000000012a10c0000730c0c68850000000000002503000000851050a9c500000000000048802400014929b932860fc1fffc000090095265c2925372650c0003fff800012012a4c3852082c4ca18000000000002402140000841010810007e00000000048000002010820210200003e00000000900000020)))) else (if i < 240 then (if i < 192 then (if i < 176 then 0x39c6363e73c1f80000000012b1af8080738c2c7ce783ff8000000025631f8180e71858f9cf07e0000000004ac63f0201ce30b9f39e0fc000000000958c7c44039c6163e73fff8000003f012b18f8182738c2c7ce7fff00000000025631f0300e71858f9cf07ff0f01f0004ac63e0351ce30b1f39e0ffe1e000000958c7c06839c6163e73c1ffc03f800012b18f80c8738c2c7ce783ff8000f80025631f0188e71858f9cf07ff000000004ac63e0301ce30b1f39e0fc1fffc0000958c7c05c39c6163e73c1f83c3f800012b18f80a8738c2c7ce783f07800000025631f0140e71858f9cf07e00ffe00004ac63e0261ce30b1f39e0fc01e000000958c7c048 else 0x2004040044000003c000001400000010400808008800000000f80028000000088010100110000000000fc050000000090020200220000000000000a0000000039e7373e73c1f83fff800012f1afccb8738c2c7ce783f0007f000025e31f0110e71858f9cf07e0000000004bc63e0201cf39b9f39e0fc1fffc0000958f7e65c39c6163e73c1ffc000000012b1cf80c0738c2c7ce783f00000000025639f0100e79cdcf9cfffe0fffe00004ac6bf36e1cf39b9f39e0fffffffe000958d7e67e39e7373e73c1ffffff800012b1afccf873ce6e7ce783f07ffff80025635f9978e79cdcf9cf07e0fffe0fc04ac6bf32e9cf39b9f39e0fc1fffc0000958d7e65c) else (if i < 208 then 0x3886261446be07c00003f014c1f00142710c4c288d7c007fff07e02983e00274e21898511af800f0fe0fc05307c004a9c43130a235f001e0001f80a60f800913886261446be0003ff83f014c1f0011a710c4c288d7c00078007e02983e00224e21898511af80000fe0fc05307c00429c43130a235f0000003ff80a60f800833886261446be00000003f014c1f00102610c08208c0000000000002980000000e21818511a0000000000005206000001c43030a234000000000000a40a000002825370654c0003fff800014012a4c3850084c088900000000000028024000008010100110f8000000000050000004010020200220003e00000000a00000020 else (if i < 224 then 0x38c6361e77fe00000003f014e1f90102714e6e2cadfff07fff07e02983f49b74e29cdc595bf81ffffe0fc05307e935e9c539b8b2b7f001fffc1f80a60fd269d3886361656fff8000003f014c1fa0182710c6c2cadfc00000007e02983f40204e218d8595bf80000000fc05307e10409c431b8b2b7f00000001f80a60fc04813886261446bfffc00003f014c1f001c2710c4c288d7ff0780007e02983e00344e21898511affe000fe0fc05307c00629c43130a235ffc000001f80a60f800c13886261446be07c3c07ff014c1f00156710c4c288d7c0f878007e02983e002a4e21898511af81f00fe0fc05307c00529c43130a235f03e0003ff80a60f800a3 else 0x39c6363e77fff83c0003f016f1ff81a2738c6c7ceffff0078007e02de3ff0324e718d8f9dfffe000fe0fc05bc7fe0629ce31b1f3bfffc00003ff80b78ffc0c339c6363e77fff8000003f016f1ff8182730c4c688d7ff0000007e02d83e00304e61898d11af80000000fc05b07c00409cf39b9f3be0fc1fffc0000b58d7e65c39c6163e77c1f80000000016b18f808042080840887ff0000000002c0000030084101081100000000000005800000001c63130e33dffc000001f80a78f800c138c6261c67be00000003f014f1f00102718c6c3ceffff0000007e029c3f80304e318d879dff80000000fc05387f00409c631b0f3bfffc000001f80a70fc80c1))) else (if i < 288 then (if i < 256 then 0x4a69730eb9c007ffff800200212a6c7894d2e61d7380007fff0004004254d8712921483ae7000000000008008421800212428055ca0000000000100100490004248510ab940000000000200200828008490a01572800f8000000400401040810921402ae500000001f008008020801212428055ca000000001f900100410014248500ab940000000000200200820008490801152000000000004004000000108210002200000000000080000000001cf39b9f3bffffffffc1f80b78ffe6fd39e7373e77fff83fff83f016f1ffcdba738c6c7ceffff0000007e02de3ff8304e718dcf9dfffe000000fc05bc7fe2609ce31b1f3bffffe00001f80b78ffc0e1 else (if i < 272 then 0x5aca521ebbc0000000000200a9084000a594a0357680000000000401501040014b290062ac001f0ffe000802a0000162965200c558003e0000001005400002052ca4018ab0000003f800200a8000008a59480315600000000000401500000016b29487aef0000000000080285208002d65290f5de0000000000100508610004a69730eb9c0003fff800200252a4c388490a0157280000000000400481200010921402ae5000000000008009020800212428855ca00000000001001204040042484008a90000003f80020024000008849080115200000000f804004800000909210022a4000000000fc8009000000a1242004548000000000010012000000 else 0x7ace661cefbe00000003f214e5f00102f59cec3dfffc00000007e429c3f04205ef3958fbef07e0000000084ae63e0203de72b1f7de0fc00000001095ac7c0407bce563efbc1f80000000212b18fa080e59c8831d600000000000421d0000001cb391063ac0000000000084390000003967220c75800000000001085c00000072ce4418eb00000000000210b4000000a594803156000f8000f80401580000894b290062ac000000fe000802b0000022965200c5580000000000100560000005aca421cab80000000000200a9400000b5d6e63d77800fffff000401525498f16badcc7aef0000fffe000802a4a930e2d65290f5de000000000010054860000)) else (if i < 304 then 0x4248510ab9400003fffff24024092a1e8490a2157280000780ffe4804812542d0921442ae5000000ffffc9009024a83a12428855ca00000003ff9201204950342484008a900000000000240240000008490a0157280000000000480401200010921402ae50000000000090080208002514b9834c60001fffc001200095261c4208510298400000000002400008080084108001107c00000000048000000201082100022007e000000009000000020210420004400001e00000120000000104208400088000000007c02400000000484108001100000000007e4800000000508210002200000000000090000000003d67330e77df00000001f90a74f80081 else (if i < 320 then 0x4a48530eb9c00000007ff240250b2a069490a61d73800f8000ffe4804a12d48d29214c3ae700000001ffc9009425a81a12428855cbffc1e003ff920120495d34248510ab97ff800007ff24024092b868490a21572fc000000ffe4804812560d0921442ae507ff0001ffc9009024ab1a12428855ca0fc1e003ff920120495534248510ab941f8003ffff24024092a8e8490a2157283f00000ffe4804812550d0921442ae5001f0f01ffc9009024a95a12428855ca003e01ffff920120495274248510ab94007c0007ff24024092a468490a2157280007fffffe4804812547d0921442ae50000f0ffffc9009024a8ba12428855ca0001e003ff92012049513 else 0x7bce573efbc1f800007ff252b58faa86f79cac7df783f000000004a5631f01018d3154abe500000001ffc9489024a81b9672a8d7da00000003ff9287204950372ce551afb400000007ff250b4092a06f59cae3df780000000ffe4a14b12540d4b29446aed001f0001ffc902b024a91a965288d5da00000003ff920560495035aca531ebbc007c0007ff240a5492a46b594a63d7780000000ffe4814a92540d6b294c7aef001f0001ffc9029434a91ad65298f5de00000003ff920528695034a69730eb9c1f83ffffff240252b6ebe94d2e61d73800fffffffe4804a56dcfd29a5cc3ae70000ffffffc90094adb8fa52439875ce00000003ff92012949503))))) else (if i < 496 then (if i < 416 then (if i < 368 then (if i < 352 then 0x4a29734698c0003fff800280012a4c389410a48d3180000000000500021080010821010220f8000000000a000000040210420204400fc00000001400000004042084040880007c0000002800000004084108081100000780000050000000041082101022000000000000a0000000003de73b9f7ffffc00003ff92b7affd5c37aef771efffe003ffffff254e5fb6f3ef59cee3dfffff00000ffe4a9cbf2570deb39dc7bfff81f0001ffc95397e4ad1bd673b8f7fff0000003ff92a72fc95837a8e6614cebe00000003f254c1f00102c498aa15fa80000000ffe4a84812540defbddcfbef07e0ffffffc94ad6bfbafbde72b9f7de0ffe0003ff9295ac7d563 else 0x5aca525ebbc007fc3f800280a94c7068b594a4bd77800ff8000005015298e0c16b29497aef001f0ffe000a02a531c162d65292f5de003e1e000014054a638285aca525ebbc007c03f800280a94c7048b594a4bd77800f8000ffe5015298e08d6b29497aef001f0001f00a02a531c112d65292f5de003e00001f94054a638215aca525ebbc007c000000280a94c7040a59480b156000f8000000501500000814b290162ac0000f0fe000a02a00000a2965202c5580000000000140540000005aca525ebbc0000000000280a10c0000b51484a91500000000000501028000010921412ae500000000000a0080208002514b9a34c6003ffffc001400095263c) else (if i < 384 then 0x5aeb735ebbc007ffff83f280a96e7c7ab5d6e6bd77800fffff00050152dcf8f16b29c97aef001f0000000a02a5b1c102d65292f5de0ffe00000014054a738605aca525ebbc007c000000280a94e7040b594a4bd7783ff8000000501529ae1816b29497aef001f0000000a02a535c102d6529af5de003e00000014054a63c205aca525ebbfffffc00000280a94c71e0b594a4bd77ffff80000005015298e3816b29497aeff81f00000fca02a531c50ad65292f5dff03e00000014054a638a05aca525ebbc1fffc00000280a94c70e0b594a4bd7783ff807f0005015298e1916b29497aef07ff0000000a02a531c302d65292f5de003ffffc0014054a6383c else (if i < 400 then 0x7ace565effc007c000000294a94c7040f7deeefdf783ffffff00052573dff9f1ef3959fbef07ff0000000a4ae73fc303de72b3f7de0fc000000014958c7c0407bce567efbc007c000000292a94c7040f59cacbdf7800f8000000521d298e081eb39597bef001f0000000a42e531c103d672b2f7de003e00000014854e638205aeb735ebbc007ffff800280ad6e7c78b594a4bd77800f807f0005015a98e0916b29497aef001f0000000a02b531c102d75b9af5de003ffffc0014054b7be3c5aeb735ebbffffffff800280a96e7df8b5d6e6bd77fc0fffff00050152dcfaf16badcd7aef07fffffe000a02a5b9f3e2d75b9af5de003fffffe014054b73e3e else 0x5aca535ebbc1ffc0007ff2c0ad4d7ac6b594a6bd77800ff800ffe5815a9af4cd6b294d7aef001f0f01ffcb02b535e95ad6529af5de003e01ffff96056a6bd275aca535ebbc007c0007ff2c0ad4d7a46b5d6e6bd77800fffff00058152dcf8f16b29497aef001f0000000b02a531c10212428a55ca003e0003ff960120495234248514ab9400000007ff2c024092a068410808110000f8000f8058000000089082101022000000000000b0000000003de73b3f7fffffe00001f94b7cfff8e17aef775efffe07ffff83f294e9fe7d7af59cecbdffffff800007e529d3f8e385eb39d97bfff81f00000fca53a7f1c50bd47332a675f00000001f94a60f80081))) else (if i < 448 then (if i < 432 then 0xb49604914200000000000818c000000169ac0932c60000000000103160000002b0d4de1d430000fffe00206004a930e520a0240a00003e00000040c00000020a414048140000003c00008180000001148280902800000007f00103000000012905012050000000001f020600000001520a0240a00000000000040c0000000084100081000000000000080000000000f59ceebdfffc0f8000ffe5a9dbfaf68def395dfbef07ff0001ffcb4af73feb1ad75b9af5de0fffffffff96056b7bf7f5aeb735ebbc007fffffff2c0ad6f7e7eb594e6bd77800f8000ffe5815adaf48d6b294d7aef001f0001ffcb02b53de91ad6529af5dff03e0003ff96056a6bda3 else 0xd6da4099ab00000000000b00a80000018cb0811352000000000016004800000338e5ce1e630000fffe002c0004a930e630c2040c41f00000000058000000080c61840818801f80000000b00000000818c3081031000007800001600000000431861020620000000fe002c000000002630c2040c40000000000058000000000fede56dffbc007c000000a98a94c7041ccb8ab17f280000000fff4b04812540fdb791267ac00000000002862a000000732e2244f48000000000050c12000000bc96269546be00000003f81cc1f0010348280902880000000000103800000002f7585afdcf07e0000000206ac63e020528a0250a00000000000040d00000000) else (if i < 464 then 0xf6de4499eb01f8003f800b18fe000089edbc8933d6000f87fff81631fc0000bbdb791267ac001f0ffe002c63f8000167b6f224cf58003e01ffe058c7f000026f6de4499eb0007c03f800b18fe000049edbc8933d60000787f001631fc000053db791267ac00000ffe002c63f8000067b6f224cf58000001ffffd8c7f000007f6de4499eb0000003ffc0b18fe00000dedbc8933d60000007f07f631fc000017db791267ac000000fe002c63f800002730e2240e40000000000058c00000000fe9e6695cebe00000003fb14c1f00103ffbcad7ff783f00000001625631f0103da7912472800000000002c4300000007b6f224cf58000000000058858000000 else (if i < 480 then 0xfeff779ffbc1f83fff800b18ff2a4cb9fdfeef3ff7800fffff001631fe5498f3fbfdde7fef0000fffe002c63fca930e7f6f334ef5c000001fc0058c7f900004fede569ffbc000003f800b18ff0c0009fdbcad3ff78000007f001631fe140013fb795a7fef000000fe002c63fc210027b6f2a4dfda000001fc0058c7f048004f6de549bfb4000003f800b18fe082009edbcab37f68000007f001631fc101013db791267acffe0f0fe002c63f80006a7b6f224cf59ffc001fc0058c7f0000c4f6de4499eb3e00003f83fb18fe00010bedbc8933d67c00007f001631fc000213db791267ac07ff00fe002c63f8000327b6f224cf580fc1e1fc0058c7f000054 else 0xf6de559bfb4007c03ffffb58fe092a4fedbcab37f68000007ffff6b1fc12541fdb791267ac000000fe002d63f800002632c28c5dca00000003ffda012049503c61840818800000000000b4000000001ffbced7ffffff0007f07f63dffff0317fbfdde7ffff800fffe0fec73ffe934eff6f334ef7dffc001fc1fd8e7ff800c5fede669defbe00003f83fb1cfff0010bedbc8933de0000007f001639fc000013fffddeffef07e0fffe002c6bfebf32e7fef2b5ffde0fc001fc0058d7fc7c044f7de44b9eb01f8003f800b1afe000089efbc8973d60000007f001635fc000013fb791a77ae000000fe002c63fe000027f6f234ef5c000001fc0058c7fa00004)))) else (if i < 576 then (if i < 528 then (if i < 512 then 0x841088810000003c00000c000000002108211102000000078000180000000022104222040000000001f03000000000142084440800000000000060000000000fede57dffbc007c03ffffbd8ff4d7a4ffdbcedbffffc0f807f07f739fff8e297ff795bffef07ff00fe002e6bff3fc327f7fbbeffde003ffffc005cc7fb73e3cfede56dffbc007c03f800b98ff4c7049edbc89b3d6000f807f001731fc000093db791367ac000000fe002e63f8000026f6d296fdde003e0000005c054a63820c61840c18800000000000b8000000001fdbcef3ffffc00007ffff6b9fff2561fff795effef07e000ffffed6bfe3eaa3ff7fbbcffde0001ffffffdac7f95b71f else 0xa5148ca14401ffc3fffc0c1f000000dd4a2919428803ff8780f8183e000001aa9452328510001ffffff0307c000001f528a4650a20003ffe03e060f8000003aa5148ca1440007c3fffc0c1f0000005d4a29194288000f8780fff83e000000ae9452328510001f0f01f0307c0000015520a4640a00000000000060c00000000bc96ae9546be00000003fc14c1f0010348291902880000000000182800000002f75a7afdcf07e0000000304ac63e020528a4650a000000000000609000000008c31bb8710c0003fff800c00012a4c3908211102007c00000000180000000202104222040007e00000003000000002042084440800003e00000060000000020) else (if i < 544 then 0xb5d68cb9670007c3c07c0c1fb00000557bad3d7eef800f8780f8183f421800aaf65a3ad51a001f0f01f0307e06000155ecb475aa34003e1e03e060fc0a0002aa5549cab754007c3c07c0c1f200900555a6b7f4ea983fffffff8183e025499fab4d6fe9d53001ffffff0307c04a931f568a5752a24003e1e03e060f8090002aad149ea754c007c3c07c0c1f010a00555a293d4ea9800f8780f8183e021080aa9452768d51001f0f01f0307c0020215528a4650a21fffffe03e060f800000faa5148ca1443fffc3c07c0c1f000001d54a291942887c0f8780fff83e000002ae9452328510f81f0f01f0307c0000055528a4650a200ffffe03e060f8000007a else (if i < 560 then 0xf7deccb9ef0007c3fffc0e1fa800005defbd9973de000f8780f81c3f500000ab9d7332a7b4001f0ffff0387c900001773ae6654f68003e1e03e070f9200002ae75cdcabfd4007c3c07c0e1f200820557bad7d7eefffff8780fff83fe3ff03aef6defedd5bf81ffffffff07f07e935fdecb575aa35fffe1e03ffe0fe0f800ebbd96aeb546be07c3fffffc1fc1f0015f7b2d5d6a8d7c0f8780fff83f83e002aed65a32c518001f0ffff0307f00000175acb4658a30003e1e03e060fe000002abdf7bfbf77c1fffffffc0c1fb1afccfd7bad3d7eef83ff87fff8183f631f01baf75a7afddf07ff0f01f0307ec63e0355aeb465cb38003e1fffe060fd800002e else 0xffdefefffffe07c3c07ffe9fe9fc7157ffbdbdffff83ff8780f81d3f739fe1abffffffffff001ffffff03a7ea5b9f1f7fef6f7fffe003e1fffe074fd4a6382effdedeffffc007c3c07c0e9fa94c7055ce3999c398000f8780f81d3e000000ab7b6b6b7eef001f0000003a02a531c10630c6460c40000000000074000000000ffdeffbffffe07c3c07ffe5fe5f92b57ffbdbf7fff83ff8780fffcbf6b1f55afbdf7febff7001ffffffff97c94adb9ff3ae6ed5fea003e1ffffff2f9204952fe75cddabfd4007c3c07ffe5f24092a57ce39994398000f8780f81cbe000000ab1963662ee500000001fff9009024a81e30c6440c40000000000072000000000))) else (if i < 624 then (if i < 592 then 0xf7deccf9ef0007c3fffc0f9ffe00005defbdbb77fe800f87fffffebffc1254bfdf7b32e7bc001f0ffff03d7ff8000177fef775ef7df03e1ffffff8ffff800afffdedebfffc1ffc3fffc0f1fff8f80ddffffff7fff800ffffff81e3ffe5498fbdf7b32e7bcf81f0ffff03c7ff8000577bef665cf780ffe1fffe078fff00006ef7deccb9ef0007fffffc0f1ffe00007defbd9973de000f87fffffe3ffc0000bfdf7b32e7bc001f0ffff03c7ff800017738e6650e60003e1fffe078f8000002ee71ccca1cc0007c3c07c0f1f00000055edbd9933d60000007f001e31fc000013186322062000000000003c0000000007fef6fffffe003e1e03fff6fd6a6bd2b else (if i < 608 then 0xce18dac798fff83c00000fe0010a01a19c31b58f31fff07800001fc0021083431863670e61ffe0f000003f800020268630c6460c41fffffe03e07f0000000fac618c8c1883fffffc0000fe0000001f18c319183107ffff87f001fc0000003d31863230620fffff001f03f800000079630c6460c41ffffe000007f0000000f0c618c8c1883ff83fff800fe0000001b98c319183107ff07f80001fc0000003631863230620ffe0f0fe003f80000006a630c6460c41ffc1e003ffff0000000d3c618c8c1883ff83c007c0fe0000001a58c319183107ff0780007ffc0000003471863230620ffe0f000003f8000000687fef6f7fffe003e1fffe07cfffa6382e else 0xdedadadfbbfffffc00000fe0a94c71e1adb591b3567ff0787f001fc1500003535b6b2366acffe0f000003f82a0000686f6d6d6fddfffc1e000007f0508600d0de9acad58abff83c00000fe0814001a19cf3f79f73fff07fffffffc04a56df7f1963672ee5fffff001ffff809024af9e32c6ce5dcbffc1e1ffffff0120495d7c658d9cbb97ff83c007fffe024092ba78cb19193527ff0787f001fc04800035319632326a4ffe0f000003f809000068632c6c65dcbffc1e000007f0100480d0c658d8cbb97ff83c00000fe0200821a19c73f78f31ffffffff001fc002549bf338e7ef1e63ffe0fffe003f8004a936e670c7562c45ffc1e000007f0009000d0)) else (if i < 640 then 0xfe9eeed5cebff83c0003fff4c1f001a3cc399983987ff07800001fe800000343ff7b7bffeffffff000003fcae73fc787fef6ffffdfffc1e003ffff95ac7d5d3fffffffffbfff83fff800ff2b1afcdb9ffbdbdfff7fff0787f001fe5631f0353ff7b7bffefffe0f000003fcac63e068738e6670e41ffc1e000007f9000000d0f69eccd1ca3ff83c3f800ff0c00001a9ed3d99a3947ff07800001fe180000343db7b3367acffe0f0fe003fc2c00006a7b6f666cf59ffc1e000007f8580000d0fe9eced5cabff83c00000ff0818001a1bdb5b7bf77fffff800ffffc15a9af7cf7befef7eeffffffffe003f82a5b9f7e6f6d6d6fddfffffe1fc007f054a638f4 else (if i < 656 then 0xf7deccf9eb3ff83c3f800ffafe0001a9fdbdbdbff7fffff87f001ff1fe98e3d3fbffff7fefffe0fffe003fe3fca936e7b6f6eedfdbffc1e1ffffffc7f0495d7f6deccd9eb3ffffc3f800ff8fe0001e9edbd99b3d67ff07fff001ff1fc000373db7b3367acffe0f0fff03fe3f80006b7b6f666cf59ffc1e1fc1fffc7f0000d5f6deccd9eb3ff83c3f800ff8fe0001a9cc399983907ff0787f001ff0000003539873330720ffe0f000003fe000000687fef7f7ffffffc1e0001fffb78ffc0d1fedefedffffffffc0003fff4e9fc71e3fdbdffbffffff07800ffffe9cbf2574ffaffff5f7bffe0fffe0fffd307e936eff4f776ae75ffc1e1fc1fffa60f800d5 else 0x1efbd99f3de7ffffffff81ffffc0003fbfe7bbbd73affffff01ffffff07c007dffef6f7fffffffffe03e07ffd8c7c0faffdedeffffffffffc07c0fffa94c71f5ceb9bbd7faffffff80fffffe481257efbcf7ff9f73fffffffff03ffc04a937f738e6670e61ffffffffe07ff800000fee71ccce1cc3fffffc07c0fff000001f5fdbdddbbdf7ff0787f07fff9ffe00357db7b3367bcffe0f0fe003ff3f80006a7fef6f7ffdfffc1e1fc007fd7fc7c0d4)))))) (i % 16)
def records (i : Nat) : Nat := field 90 (if i < 2016 then (if i < 1008 then (if i < 496 then (if i < 240 then (if i < 112 then (if i < 48 then (if i < 16 then 0x94a0a719684b4c8270420e652829c65a12d3209c1083294a0a719684b4c8270420b252829c65a12d3209c1082494a0a719684b4c8270420700094a0a719684b4c81081694a0a719684b4c8270420580094a0a7192d3209c1080d94a0a719684b4c82704203652829c65a12d3209c1080994a0a719684b4c8270420180094a0a5a12d3209c1080594a0a719684b4c82704201652829c65a12d3209c1080394a0a719684b4c8270420080094a0a719684b4c827042 else (if i < 32 then 0x94a0a719685092d3209c10a52829c65a12d488c82704294a0a719684b50b3209c10a52829c65a12d404c82704294a0a719684b4f83209c10a52829c65a12d3b0c82704294a0a719684b4dd3209c10a52829c65a12d320bd2704294a0a719684b4c82c49c10a52829c65a12d3209c2384294a0a719684b4c82708310a52829c65a12d3209c1e44294a0a719684b4c82706e10a52829c65a12d3209c1884294a0a719684b4c82705910a52829c65a12d3209c13c42 else 0x94a1a829c65a12d3209c10a52829fd719684b4c82704294a0a7e1c65a12d3209c10a52829ef719684b4c82704294a0a7a1c65a12d3209c10a52829e5719684b4c82704294a0a779c65a12d3209c10a52829c66e5684b4c82704294a0a719a95a12d3209c10a52829c6671684b4c82704294a0a719925a12d3209c10a52829c6639684b4c82704294a0a7197f5a12d3209c10a52829c65a15a4b4c82704294a0a719685552d3209c10a52829c65a1504b4c827042)) else (if i < 80 then (if i < 64 then 0x252829c66712d3209c1080094a0a7197f4b4c8270420028894a0a5a12d3209c1080094a46829684b4c827042a5252829c65a12d3209c10a8894a0a719684b4c827042a0252829c65a12d3209c10a7a94a0a719684b4c8270429c252829c65a12d3209c10a6894a0a719684b4c82704298a52829c65a12d3209c10a5291a0a719684b4c82704294a3c829c65a12d3209c10a528d20a719684b4c82704294a27829c65a12d3209c10a5288a0a719684b4c827042 else 0xa2252829684b4c82704200a5291a0a5a12d3209c1080294a0a71d684b4c82704200a5282dc65a12d3209c1080294e0a719684b4c82704200a52829c65a12d270420700294a0a719684b4c81081600a52829c64b4c8270420340294a0a5a12d3209c1080500a52829c65a0c82704200c0294a0a719684b4c82704200652829c65a12d320420580194a0a7192d3209c1080d00652829684b4c8270420140100252829c65a12d3b0c81080094a0a719684b4c82c442) else (if i < 96 then 0x94a0a719684b4c81081600e52829c64b4c8270420340394a0a5a12d3209c1080500e52829c65a12d3209c10c0200252829c65a12d3b04200a52829c65a12d3b0c81080294a0a719684b4c82c44200a52829c65a12d3209d1080294a0a719684b4ec2704200a52829c65a12d3749c1080200252829c6670c82704200a52829c6671683209c1080294a0a71968508c82704200a52829c66712d3209c1080294a0a7197f4b4c82704200a52829c65a52d3209c10802 else 0x252829c65a0c8270420125289e0a719683209c1080494a0a719684b4c82704201252829c65a12d3209c1100394a0a719684b4ec3204200e52829c65a12d320b11080394a0a719684b4c82784200e52829c65a12d3249c108039a252829c65a0c82704200e52829c66712d3209c1080394a0a7197f4b4c82704200e52829c65a92d3209c10803a2252829684b4c82704200e5291a0a5a12d3209c1080394a0a721684b4c82704200e54829c65a12d3209c10803))) else (if i < 176 then (if i < 144 then (if i < 128 then 0x94a0a5a12d3209c1884201652829684b4c8270591080594a0a5a12d3209c13c4201652829684b4c8270420e40594a0a5a12d3209c1083201652829684b4c8270420b00594a0a5a12d3209c1082401652829684b4c8270420700500252829684b4c81081601652829c65a12d320420580594a0a5a12d3209c108160140094a0a4b4c8270420340594a0a7192d3209c1080d01652829684b4c8270420340594a0a5a12d3209c1080901652829684b4c82704201805 else 0x94a0a5a1424b4c82704201652829684b92d3209c1080594a0a5a12d488c82704201652829684b50b3209c1080594a0a5a12d404c82704201652829684b4f83209c1080594a0a5a12d3b0c82704201652829684b4dd3209c1080594a0a5a12d328c82704201652829684b4c82f49c1080594a0a5a12d320b12704201652829684b4c82809c1080594a0a5a12d3209c2384201652829684b4c8270831080594a0a5a12d3209c1e44201652829684b4c82706e10805) else (if i < 160 then 0x94a0a7bd684b4c82704201652829e85a12d3209c1080594a0a795684b4c82704201652829de5a12d3209c1080594a0c719684b4c82704201656829c65a12d3209c1080594a0a6e5684b4c82704201652829a95a12d3209c1080594a0a671684b4c82704201652829925a12d3209c1080594a0a639684b4c827042016528297f5a12d3209c1080594a0a5b1684b4c82704201652829685692d3209c1080594a0a5a1554b4c82704201652829685412d3209c10805 else 0xa2252829684b4c8270420168094a0a5a12d3209c108059ea52829684b4c8270420167094a0a5a12d3209c108059a252829684b4c8270420166294a0a5a12d3209c1080595a52829684b4c8270420165291a0a5a12d3209c1080594a3c829684b4c827042016528d20a5a12d3209c1080594a27829684b4c8270420165288a0a5a12d3209c1080594a1a829684b4c827042016528320a5a12d3209c1080594a0a7f5684b4c82704201652829f85a12d3209c10805)) else (if i < 208 then (if i < 192 then 0x94a0a719684b4c82c4420140094a0a5a12d320a01080594a0a719684b4c8280420140094a0a5a12d3289c1080594a0a719684b4ca270420140094a0a5a12e3209c1080594a0a719684b8c8270420140094a0a6712d3209c1080594a0a7199c4b4c8270420140094a0a5fd2d3209c1080594a0a7197f4b4c8270420140094a0a5b12d3209c1080594a0a7196c4b4c8270420140094a0c5a12d3209c1080500256829684b4c8270420169494a0a5a12d3209c10805 else 0x94a0a719684b4c82c44201a52829c65a12d320a11080694a0a719684b4cb2704201a52829c65a12f3209c1080694a0a7199c4b4c82704201a52829c65fd2d3209c1080694a0a7196d4b4c82704201a8894a0a5a12d3209c1080694a46829684b4c82704201a52829ca5a12d3209c1080695e0a719684b4c82704201a52829c65a12d320420580694a0a7192d3209c1080d0180094a0a5a12d3b0c81080594a0a719684b4ec320420140094a0a5a12d320b110805) else (if i < 224 then 0x94a0a719684b4cd2704202652829c65a1313209c1080994a0a7199c4b4c82704202652829c65fd2d3209c1080994a0a7196f4b4c8270420268894a0a5a12d3209c1080994a46829684b4c82704202652829cb5a12d3209c1080994a0d719684b4c82704202652829c65a12d320420580994a0a7192d3209c1080d0240094a0a5a12d3209c1080894a46829684b4c82704202252829c65a12d3209c1080894a0a719684b4c82704201e52829c65a12d3b0c810806 else 0x94a0a7192d3209c1184203652829c64b4c8270420e40d94a0a7192d3209c1083203652829c64b4c8270420b00d94a0a7192d3209c1082403652829c64b4c8270420700d00252829c64b4c81081603652829c65a12d320420580d94a0a7192d3209c1081603652829c65a12d3209c1080ba2252829684b4c8270420280094a0a5a12d3209c1080a94a0a719684b4c82704202a52829c65a12d3b0c81080994a0a719684b4c82c44202652829c65a12d320a310809)))) else (if i < 368 then (if i < 304 then (if i < 272 then (if i < 256 then 0x94a0a7192d42cc82704203652829c64b5013209c1080d94a0a7192d3e0c82704203652829c64b4ec3209c1080d94a0a7192d374c82704203652829c64b4d03209c1080d94a0a7192d320bd2704203652829c64b4c82c49c1080d94a0a7192d320a62704203652829c64b4c82708e1080d94a0a7192d3209c20c4203652829c64b4c8270791080d94a0a7192d3209c1b84203652829c64b4c8270621080d94a0a7192d3209c1644203652829c64b4c82704f1080d else 0x94a0a719b94b4c82704203652829c66a52d3209c1080d94a0a7199c4b4c82704203652829c66492d3209c1080d94a0a7198e4b4c82704203652829c65fd2d3209c1080da2252829684b4c8270420365291a0a5a12d3209c1080d94a0a731684b4c82704203659829c65a12d3209c1080d94a0a7195a4b4c82704203652829c65552d3209c1080d94a0a719504b4c82704203652829c65092d3209c1080d94a0a719344b4c82704203652829c64b5223209c1080d) else (if i < 288 then 0x9a252829c64b4c8270420366294a0a7192d3209c1080d96652829c64b4c8270420365291a0a7192d3209c1080d94a3c829c64b4c827042036528d20a7192d3209c1080d94a27829c64b4c8270420365288a0a7192d3209c1080d94a1a829c64b4c82704203652829fd7192d3209c1080d94a0a7e1c64b4c82704203652829ef7192d3209c1080d94a0a7a1c64b4c82704203652829e57192d3209c1080d94a0a779c64b4c82704203652829cc7192d3209c1080d else 0x94a0a719684b4c82c4420340094a0a7192d320a61080d94a0a719684b4c8298420340094a0a7192d3409c1080d94a0a719684b4d0270420340094a0a719343209c1080d94a0a719684d0c82704203400a22528292d3209c1080d0025291a0a4b4c8270420340094a0a7312d3209c1080d00259829c64b4c8270420369494a0a7192d3209c1080da2252829c64b4c8270420368094a0a7192d3209c1080d9ea52829c64b4c8270420367094a0a7192d3209c1080d)) else (if i < 336 then (if i < 320 then 0x94a0a719684b4c81083905a52829c65a12d320420c81694a0a719684b4c81082c05a52829c65a12d320420901694a0a719684b4c81081c0580094a0a7192d3209c1081194a0a7197f4b4c82704204652829c65a12d3209c1081100252829c64b4c82704203a52829c66712d3209c1080e94a0a719684b4c8270420380094a0a7192d3209c1180d94a0a719684b4c8270460340094a0a7192d3b0c81080d94a0a719684b4ec320420340094a0a7192d320b11080d else 0x94a0a719684dcc82704205a52829c66712d3209c1081694a0a7197f4b4c82704205a52829c65c92d3209c10816a2252829684b4c82704205a5291a0a5a12d3209c1081694a0a741684b4c82704205a5283dc65a12d3209c1081694a0a719684b4c82384205a52829c65a12d320831081694a0a719684b4c81e44205a52829c65a12d3206e1081694a0a719684b4c81884205a52829c65a12d320591081694a0a719684b4c813c4205a52829c65a12d3204810816) else (if i < 352 then 0x94a0a719725a12d3204205a52829c65a15a4b4c81081694a0a719685552d3204205a52829c65a1504b4c81081694a0a719685092d3204205a52829c65a1374b4c81081694a0a719684b5223204205a52829c65a12d42cc81081694a0a719684b5013204205a52829c65a12d3e0c81081694a0a719684b4ec3204205a52829c65a12d374c81081694a0a719684b4d53204205a52829c65a12d320bd1081694a0a719684b4c82c44205a52829c65a12d3549c10816 else 0x94a22829c65a12d3204205a5286a0a719684b4c81081694a0f829c65a12d3204205a52829fd719684b4c81081694a0a7e1c65a12d3204205a52829ef719684b4c81081694a0a7a1c65a12d3204205a52829e5719684b4c81081694a0a779c65a12d3204205a52829d0719684b4c81081694a0a719b95a12d3204205a52829c66a5684b4c81081694a0a7199c5a12d3204205a52829c6649684b4c81081694a0a7198e5a12d3204205a52829c65fd684b4c810816))) else (if i < 432 then (if i < 400 then (if i < 384 then 0x252829c65c92d3204205800a2252829684b4c8108160025291a0a5a12d320420580094a0a741684b4c8108160025283dc65a12d3204205a9494a0a719684b4c810816a2252829c65a12d3204205a8094a0a719684b4c8108169ea52829c65a12d3204205a7094a0a719684b4c8108169a252829c65a12d3204205a6294a0a719684b4c81081694a46829c65a12d3204205a528f20a719684b4c81081694a34829c65a12d3204205a5289e0a719684b4c810816 else 0x94a0a7199c4b4c82704207252829c65fd2d3209c1081c94a0a719754b4c8270420728894a0a5a12d3209c1081c94a46829684b4c82704207252829d35a12d3209c1081c94a12719684b4c8270420700094a0a719684b4c81081894a0a719684b4c82c44206252829c65a12d3209c1081800252829c65a12d3204805a52829c65a12d3209c1201600252829c65a12d354420580094a0a719684dcc81081600252829c66712d320420580094a0a7197f4b4c810816) else (if i < 416 then 0xa2252829684b4c8270420925291a0a5a12d3209c1082494a0a719684b4c82704208c0094a0a719684b4c81081f94a0a719684b4ec3204207e52829c65a12d3209c1081f94a0a719684b4c82704207a6894a0a719684b49c1081d00252829c65a12d2704207652829c65a12d3209c1081d94a0a719684b4c82704a07252829c65a12d3b0c81081c94a0a719684b4c82c44207252829c65a12d320ab1081c94a27829c65a12d2704207252829c65a13b3209c1081c else 0x94a0a7197f4b4c8270420b28894a0a5a12d3209c1082c94a46829684b4c8270420b252829c65a12d3209c1082b94a0a719684b4c8270420aa52829c65a12d3209c1082994a0a719684b4c8270420a252829c65a12d3209c1082794a0a719684b4c82704209a52829c65a12d3209c1082594a0a719684b4ec3204209252829c65a12d320b11082494a0a719684b4c82b44209252829c66712d3209c1082494a0a7197f4b4c82704209252829c65e52d3209c10824)) else (if i < 464 then (if i < 448 then 0x94a0a7197f4b4c8270420ca52829c65f12d3209c10832a2252829684b4c8270420ca5291a0a5a12d3209c1083294a0a7199c4b4c8270420c652829c65a12d3209c1083100252829c64b4c8270420c25286a0a7192d3209c1083094a0a719684b4c8270420c252829c65a12d3209c1082f94a0a719684b4c8270420ba52829c65a12d3209c1082d94a0a719684b4ec320420b252829c65a12d320b11082c94a0a719684b4c82b8420b252829c66712d3209c1082c else 0x94a0a7199c4b4c8270420e652829c65fd2d3209c1083994a0a7197e4b4c8270420e68894a0a5a12d3209c1083994a46829684b4c8270420e652829c65a12d3209c1083894a0a719684b4c8270420de6294a0a719684b4c81083600252829c65a12d320420da52829c65a12d3209c1083694a0a719684b4c8270420d652829c65a12d3209c1083494a0a719684b4c8270420ce52829c65a12d3b0c81083294a0a719684b4c82c4420ca52829c66712d3209c10832) else (if i < 480 then 0x252829c64b4c82704610a52829c65a12d3209c1184294a0a719684b4c82704410a52829c65a12d3209c10c4294a0a719684b4ec3204210652829c65a12d3209c1084194a0a719684b4c82704210252829c65a12d3209c1083f94a0a719684b4c8270420fa52829c65a12d3209c1083d94a0a719684b4c8270420f252829c65a12d3209c1083b94a0a719684b4c8270420ea52829c65a12d3b0c81083994a0a719684b4c82c4420e652829c65a12d320b010839 else 0x94a0a719684b4c82705210a52829c65a12d3209c1444294a0a719684b4ec3205010a52829c65a12d3209c1404294a0a719684b4ec3204f10a52829c65a12d320b113c4294a0a7199c4b4c82704f10a52829c65fd2d3209c13c4294a0a7197a4b4c82704f10a8894a0a5a12d3209c13c4294a46829684b4c82704f10a52829c65a12d3209c1384294a0a719684b4c82704d10a52829c65a12d3209c1284200252829c65a12d3204810a52829c65a12d3209c12042))))) else (if i < 752 then (if i < 624 then (if i < 560 then (if i < 528 then (if i < 512 then 0x94a0a719684b4c82705a10a52829c65a12d3b0c81644294a0a719684b4c82dc5910a52829c65a12d320b11644294a0a7199c4b4c82705910a52829c65fd2d3209c16442a2252829684b4c82705910a5291a0a5a12d3209c1644294a0a719684b4c82705810a52829c65a12d3209c15c4294a0a719684b4c82705510a52829c65a12d3209c1504294a0a719684b4c82c45310a52829c65a12d3209c14c429a252829c65a12d320521080094a0a719684b4c814842 else 0x94a0a719684b4ec3206210a52829c65a12d320b11884294a0a7199c4b4c82706210a52829c65fd2d3209c18842a2252829684b4c82706210a5291a0a5a12d3209c1884294a0a719684b4c82706110a52829c65a12d3209c17c4294a0a7197f4b4c82705e10a52829c65a12d3209c1784294a0a719684b4c82705d10a52829c65a12d3209c1704200252829c64b4c82705b10a5289e0a7192d3209c16c4294a0a719684b4c82705b10a52829c66712d3209c16842) else (if i < 544 then 0x94a0a719684b4c82706c10a52829c65a12d3b0c81ac4294a0a719684b4c82706b10a52829c65a12d3209c1a04294a0a7197f4b4c82706710a52829c65a12d3209c19c4294a0a7199c4b4c82706610a52829c65a12d3209c1984294a0a719684b4c82c46510a52829c65a12d3209c194429c252829c65a12d320641080094a0a719684b4c81904294a0a719684b4c8270641080094a0a7192d3209c18c4294a22829c64b4c82706310a52829c65a12d3209c18c42 else 0x94a0a719684b4c82707410a52829c65a12d320b11cc4294a0a719684b4c82707310a52829c65a12d3209c1c84294a0a719684b4c82707110a8094a0a719684b4c81c04200252829c65a12d3207010a52829c65a12d3209c1c04294a0a719684b4c82706f10a52829c65a12d3b0c81b84294a0a719684b4c82c46e10a52829c66712d3209c1b84294a0a7197f4b4c82706e10a8894a0a5a12d3209c1b84294a46829684b4c82706e10a52829c65a12d3209c1b442)) else (if i < 592 then (if i < 576 then 0xa2252829684b4c82707b10a52829c65a12d3209c1ec4200252829684b4c82c47a10a52829c65a12d320b11e84200252829684b4c82707a10a52829c65a12d3209c1e84294a0a5a12d320b12707a10a52829c65a12d3b0c81e44294a0a719684b4c82c47910a52829c66712d3209c1e44294a0a7197f4b4c82707910a8894a0a5a12d3209c1e44294a46829684b4c82707910a52829c65a12d3209c1e04294a0a719684b4c82707710a52829c65a12d3209c1d842 else 0x94a0a719684b4c82708410a52829c65a12d3b0c820c4294a0a719684b4c82e88310a52829c65a12d320b120c4294a0a7199c4b4c82708310a52829c65fd2d3209c20c42a2252829684b4c82708310a5291a0a5a12d3209c20c4294a0a719684b4c82708210a52829c65a12d3209c2004294a0a719684b4c82707f10a52829c65a12d3209c1f84294a0a719684b4c82707d10800a2252829684b4c81ec42a2252829c65a12d3207b1080094a0a719684b4c81ec42) else (if i < 608 then 0x94a0a7199c4b4c82708e10a52829c65fd2d3209c23842a2252829684b4c82708e10a5291a0a5a12d3209c2384294a0a78d684b4c82708e10a52829c65a12d3b0c822c4294a0a719684b4c82708b10a52829c65a12d3209c2284294a0a719684b4c82708910a52829c65a12d3209c2204294a0a719684b4c82708710a8894a0a5a12d3209c2184294a0a719684b4c8270861080094a0a5a12d3209c2144294a0a719684b4c82708510a52829684b4dd3209c21442 else 0x94a0a719684b4c82709910a52829c65a12d3209c2604294a0a719684b4c82709710a52829c65a12d3209c2584294a0a719684b4c82709410a52829c65a12d3209c24c42a5252829c65a12d320921080094a0a719684b4c82484294a0a719684b4c82709210a52829c65a12d3209c2444294a0a719684b4c82c49010a52829c65a12d3209c2404294a0a719684b4c82708f10a52829c65a12d3b0c82384294a0a719684b4c82c48e10a52829c65a12d3a89c23842))) else (if i < 688 then (if i < 656 then (if i < 640 then 0x94a0a719684b4c82dc9c10a52829c66712d320b12704294a0a7197f4b4c82c49c10a8894a0a5a12d320b12704294a46829684b4c82c49c10a52829c65a12d320b02704294a0a719684b4c82b89c10a52829c65a12d320ad2704294a0a719684b4c82ac9c10a52829c65a12d320a62704294a0a719684b4c828c9c10a52829c65a12d320a12704294a0a719684b4c82809c10a52829c65a12d3209e2704294a0a719684b4c82749c10a5291a0a5a12d3209c26442 else 0x94a0a719684b4c831c9c10a52829c65a12d320c62704294a0a719684b4c83149c10a52829c65a12d320c42704294a0a719684b4c830c9c10a52829c65a12d320c22704294a0a719684b4c83049c10a52829c65a12d320c02704294a0a719684b4c82fc9c10a52829c65a12d320be2704294a0a7199c4b4c82f49c10a52829c65fd2d320bd27042a2252829684b4c82f49c10a5291a0a5a12d320bd2704294a0a79d684b4c82f49c10a52829c65a12d320ba27042) else (if i < 672 then 0x94a0a719684b4e23209c10a52829c65a12d380c82704294a0a7199c4b4dd3209c10a52829c65fd2d374c827042a2252829684b4dd3209c10a5291a0a5a12d374c82704294a0a719684b4db3209c10a52829c65a12d368c82704294a0a719684b4d93209c10a52829c65a12d354c82704294a0a719684b4d03209c10a52829c65a12d334c82704294a0a719684b4cb3209c10a52829c65a12d328c82704294a0a719684b4c93209c10a5291a0a5a12d320c727042 else 0x94a0a719684b4f93209c10a52829c66712d3e0c82704294a0a7197f4b4f83209c10a8894a0a5a12d3e0c82704294a46829684b4f83209c10a52829c65a12d3dcc82704294a0a719684b4f63209c10a52829c65a12d3d0c82704294a0a7199c4b4ec3209c10a52829c65fd2d3b0c827042a2252829684b4ec3209c10a5291a0a5a12d3b0c82704294a0a719684b4ea3209c10a52829c65a12d3a0c82704294a0a719684b4e63209c10a52829c65a12d390c827042)) else (if i < 720 then (if i < 704 then 0x94a0a719684b5033209c10a52829c65a12d408c82704294a0a7199c4b5013209c10a52829c66192d404c82704294a0a7197f4b5013209c10a8894a0a5a12d404c82704294a46829684b5013209c10a52829c65a12d3fcc82704294a0a719684b4fe3209c10a52829c65a12d3f4c82704294a0a7197f4b4fc3209c10a52829c65a12d3f0c82704200252829c64b4fb3209c10a528d20a7192d3ecc82704294a0a719684b4fb3209c10a52829c65a12d3e8c827042 else 0x94a0a719684b50c3209c10a528297f5a12d430c82704294a0a7199c4b50b3209c10a52829c65fd2d42cc827042a2252829684b50b3209c10a5291a0a5a12d42cc82704294a0a719684b50a3209c10a52829c65a12d424c82704294a0a719684b5083209c10a52829c65a12d41cc82704294a0a719684b5063209c10a52829c65a12d414c82704200252829684b5043209c10a52829c65a12d410c82704294a0a5a1424b5043209c10a5291a0a5a12d40cc827042) else (if i < 736 then 0x94a0a719684b5183209c10a52829c66712d454c82704294a0a719684b5153209c10a52829c65a12d450c82704294a0a719684b5123209c10a52829c65a12d444c82704294a0a719684b5103209c10a52829c65a12d43cc8270420025291a0a4b50d3209c1080094a0a7192d434c82704294a46829c64b50d3209c10a5291a0a5a12d434c82704294a0a719684b50d3209c1080094a0a5fd2d430c82704294a0a7197f4b50c3209c1080094a0a5a12d430c827042 else 0x94a0a719684b5233209c10a52829c66712d488c82704294a0a7199a4b5223209c10a52829c65fd2d488c827042a2252829684b5223209c10a5291a0a5a12d488c82704294a0a7b9684b5223209c10a52829c65a12d484c82704294a0a719684b5203209c10a52829c65a12d47cc82704294a0a719684b51e3209c10a52829c65a12d474c82704294a0a719684b51c3209c10a52829c65a12d46cc82704294a0a719684b51a3209c10a52829c65a12d464c827042)))) else (if i < 880 then (if i < 816 then (if i < 784 then (if i < 768 then 0x94a0a719684dd2d3209c1080094a0a719344b4c82704294a0a719684d12d3209c10a52829c65a1314b4c82704294a0a719684bd2d3209c10a52829c65a12e4b4c827042a2252829684b52c3209c10a52829c65a12d4b0c82704294a0a719684b52b3209c10a52829c65a12d4a8c82704294a0a719684b5293209c10a52829c65a12d4a0c82704294a0a719684b5273209c10a52829c65a12d498c82704294a0a719684b5253209c10a52829c65a12d490c827042 else 0x94a0a719685392d3209c10a52829c65a14d4b4c82704294a0a719685312d3209c10a52829c65a14b4b4c82704294a0a719685252d3209c10a52829c65a1474b4c82704294a0a719685152d3209c10a52829c6691424b4c82704294a0a7199c5092d3209c10a52829c65fd424b4c827042a2252829685092d3209c10a5291a0a5a1424b4c82704294a0a719685052d3209c10a52829c65a1404b4c82704294a0a719684f92d3209c10a52829c65a13b4b4c827042) else (if i < 800 then 0x94a46829685692d3209c10a52829f65a15a4b4c82704294a0a719685652d3209c10a52829c65a1584b4c82704294a0a7199c5552d3209c10a52829c65fd554b4c827042a2252829685552d3209c10a5291a0a5a1554b4c82704294a0a719685512d3209c10a52829c65a1534b4c82704294a0a719685492d3209c10a52829c6671504b4c82704294a0a7197f5412d3209c10a8894a0a5a1504b4c82704294a46829685412d3209c10a52829c65a14f4b4c827042 else 0x94a0a719685952d3209c10a52829c65a1644b4c82704294a0a7196858d2d3209c10a52829c65a1624b4c82704294a0a719685812d3209c10a52829c65a15f4b4c82704294a0a719685792d3209c10a52829c65a15d4b4c827042a5252829c65712d3209c1080094a0a7195c4b4c82704294a0a719685712d3209c10a52829c65fd5b4b4c82704294a0a7196856d2d3209c10a52829c66715a4b4c82704294a0a7197f5692d3209c10a8894a0a5a15a4b4c827042)) else (if i < 848 then (if i < 832 then 0x94a0a719895a12d3209c10a52829c6619684b4c827042a22528297f5a12d3209c10a5291a0a5fd684b4c82704294a0a7197e5a12d3209c10a52829c65f1684b4c82704294a0a7197a5a12d3209c10a52829c65e5684b4c82704294a0a719755a12d3209c10a52829c65c9684b4c82704294a0a7196f5a12d3209c10a52829c65b5684b4c82704294a0a7196c5a12d3209c10a52829c65a9684b4c82704294a0a719695a12d3209c10a8894a0a5a1654b4c827042 else 0x94a0a7199a5a12d3209c10a52829c6661684b4c82704294a0a719965a12d3209c10a52829c6655684b4c82704294a0a719945a12d3209c10a8894a0a649684b4c82704294a46829925a12d3209c10a52829c6645684b4c82704294a0a719905a12d3209c10a52829c663d684b4c827042a22528298e5a12d3209c10a5291a0a639684b4c82704294a0a7198d5a12d3209c10a52829c6631684b4c82704294a0a7198b5a12d3209c10a52829c6629684b4c827042) else (if i < 864 then 0x94a0a719af5a12d3209c10a52829c66b9684b4c82704294a0a719ad5a12d3209c10a52829c66b1684b4c82704200252829ab5a12d3209c10a5286a0a6ad684b4c82704294a0a719ab5a12d3209c10a52829c66a9684b4c827042a2252829a95a12d3209c10a5291a0a6a5684b4c82704294a0a719a85a12d3209c10a52829c669d684b4c82704294a0a719a65a12d3209c10a52829c6691684b4c827042a22528299c5a12d3209c10a5291a0a671684b4c827042 else 0x94a0a719bc5a12d3209c10a52829c66ed684b4c82704298a52829ba5a12d3209c1080094a0a6e9684b4c82704294a0a719ba5a12d3209c10a8894a0a6e5684b4c82704294a46829b95a12d3209c10a52829c66e1684b4c82704294a0a719b75a12d3209c10a52829c66d9684b4c82704294a0a719b55a12d3209c10a52829c66d1684b4c82704294a0a719b35a12d3209c10a52829c66c9684b4c82704294a0a719b15a12d3209c10a52829c66c1684b4c827042))) else (if i < 944 then (if i < 912 then (if i < 896 then 0x94a0a74dc65a12d3209c10a52829d0719684b4c82704294a0a731c65a12d3209c10a52829cb719684b4c82704294a0a729c65a12d3209c10a52829c8719684b4c82704294a0a71dc65a12d3209c10a52829c6715684b4c82704294a0a719c45a12d3209c10a52829c670d684b4c82704294a0a719c25a12d3209c10a52829c6705684b4c82704294a0a719c05a12d3209c10a52829c66fd684b4c82704294a0a719be5a12d3209c10a52829c66f5684b4c827042 else 0x94a0a7b5c65a12d3209c10a52829ec719684b4c82704294a0a7adc65a12d3209c10a52829ea719684b4c82704294a0a79dc65a12d3209c10a52829e6719684b4c82704294a0a78dc65a12d3209c10a52829e2719684b4c82704294a0a785c65a12d3209c10a52829dd719684b4c82704294a0a771c65a12d3209c10a52829db719684b4c82704294a0a769c65a12d3209c10a52829d9719684b4c82704294a0a761c65a12d3209c10a52829d7719684b4c827042) else (if i < 928 then 0x94a0a809c65a12d3209c10a5282a01719684b4c82704294a0a801c65a12d3209c10a52829ff719684b4c82704294a0a7f9c65a12d3209c10a52829fc719684b4c82704294a0a7edc65a12d3209c10a52829fa719684b4c82704294a0a7e5c65a12d3209c10a52829f6719684b4c82704294a0a7d5c65a12d3209c10a52829f4719684b4c82704294a0a7cdc65a12d3209c10a52829f2719684b4c82704294a0a7c5c65a12d3209c10a52829ee719684b4c827042 else 0x94a19829c65a12d3209c10a528620a719684b4c82704294a17829c65a12d3209c10a5285a0a719684b4c82704294a12829c65a12d3209c10a5283e0a719684b4c82704294a0d829c65a12d3209c10a528320a719684b4c82704294a0b829c65a12d3209c10a5282a09719684b4c82704294a0a821c65a12d3209c10a5282a07719684b4c82704294a0a819c65a12d3209c10a5282a05719684b4c82704294a0a811c65a12d3209c10a5282a03719684b4c827042)) else (if i < 976 then (if i < 960 then 0x94a36829c65a12d3209c10a528ce0a719684b4c82704294a32829c65a12d3209c10a528c60a719684b4c82704294a2f829c65a12d3209c10a528b60a719684b4c82704294a2c829c65a12d3209c10a528ae0a719684b4c82704294a2a829c65a12d3209c10a528960a719684b4c82704294a24829c65a12d3209c10a528820a719684b4c82704294a1f829c65a12d3209c10a5287a0a719684b4c82704294a1d829c65a12d3209c10a528720a719684b4c827042 else 0x94a4f829c65a12d3209c10a529360a719684b4c82704294a4c829c65a12d3209c10a5292e0a719684b4c82704294a44829c65a12d3209c10a5290e0a719684b4c82704294a42829c65a12d3209c10a529060a719684b4c82704294a40829c65a12d3209c10a528fe0a719684b4c82704294a3e829c65a12d3209c10a528ee0a719684b4c82704294a3a829c65a12d3209c10a528e60a719684b4c82704294a38829c65a12d3209c10a528de0a719684b4c827042) else (if i < 992 then 0x9b652829c65a12d3209c10a6c94a0a719684b4c8270429ae52829c65a12d3209c10a6694a0a719684b4c82704299652829c65a12d3209c10a6494a0a719684b4c82704298652829c65a12d3209c10a6094a0a719684b4c82704297e52829c65a12d3209c10a5e94a0a719684b4c82704296652829c65a12d3209c10a5794a0a719684b4c82704295a52829c65a12d3209c10a5494a0a719684b4c82704294e52829c65a12d3209c10a529460a719684b4c827042 else 0xa1a52829c65a12d3209c10a8594a0a719684b4c827042a1252829c65a12d3209c10a8394a0a719684b4c827042a0a52829c65a12d3209c10a7f94a0a719684b4c8270429fa52829c65a12d3209c10a7d94a0a719684b4c8270429f252829c65a12d3209c10a7994a0a719684b4c8270429de52829c65a12d3209c10a7594a0a719684b4c8270429d252829c65a12d3209c10a7394a0a719684b4c8270429ca52829c65a12d3209c10a6e94a0a719684b4c827042)))))) else (if i < 1504 then (if i < 1248 then (if i < 1120 then (if i < 1056 then (if i < 1024 then 0x259829c65a12d3209c1080095e0a719684b4c82704200256829c65a12d3209c108009520a719684b4c82704200253829c65a12d3209c10a9b94a0a719684b4c827042a6a52829c65a12d3209c10a9994a0a719684b4c827042a6252829c65a12d3209c10a9794a0a719684b4c827042a5a52829c65a12d3209c10a9394a0a719684b4c827042a4652829c65a12d3209c10a8f94a0a719684b4c827042a3a52829c65a12d3209c10a8d94a0a719684b4c827042 else (if i < 1040 then 0x252829c75a12d3209c10a9494a27719684b4c82704294a3489dc65a12d3209c10a9494a22719684b4c827042a5252869c65a12d3209c10a5291a1a719684b4c82704200252849c65a12d3209c1080094a0f719684b4c82704200252835c65a12d3209c1080094a0c719684b4c8270420025282dc65a12d3209c10a949c20a719684b4c827042a5268829c65a12d3209c10a809a20a719684b4c827042a5262829c65a12d3209c10a8898a0a719684b4c827042 else 0x252829ee5a12d3209c10a8894a0a7a1684b4c82704294a46829e85a12d3209c10a52829ef7a1684b4c82704200252829e75a12d3209c10a8894a0a795684b4c82704294a46829e55a12d3209c1080094a0a78d684b4c827042a2252829de5a12d3209c10a5291a0a779684b4c82704200252829d35a12d3209c1080094a0a741684b4c82704200252829cc5a12d3209c1080094a0a72d684b4c82704200252829ca5a12d3209c1080094a0a721684b4c827042)) else (if i < 1088 then (if i < 1072 then 0xa225289e0a5a12d3209c10a5291a27829684b4c827042a225288a0a5a12d3209c10a5291a22829684b4c827042a225286a0a5a12d3209c10a5291a1a829684b4c827042002528320a5a12d3209c10a8894a0a825684b4c827042a2252829fd5a12d3209c10a5291a0a7f5684b4c82704294a43829fd5a12d3209c10a8894a0a7e1684b4c82704294a46829f85a12d3209c1080094a0a7d9684b4c827042a2252829ef5a12d3209c10a5291a0a7bd684b4c827042 else 0xa025291a0a5a12d3209c10a7a94a46829684b4c8270429c25291a0a5a12d3209c10a6894a46829684b4c82704298a5291a0a5a12d3209c10a5294646829684b4c82704294a4f91a0a5a12d3209c10a5293646829684b4c82704294a4c91a0a5a12d3209c10a5292e46829684b4c8270420025290e0a5a12d3209c10a5291a42829684b4c827042a22528f20a5a12d3209c10a5291a3c829684b4c827042a22528d20a5a12d3209c10a5291a34829684b4c827042) else (if i < 1104 then 0xa6e8894a0a5a12d3209c10a94a2252829684b4c827042a4e8894a0a5a12d3209c10a91a2252829684b4c827042a3e8894a0a5a12d3209c10a8ea2252829684b4c827042a368894a0a5a12d3209c10a88a0252829684b4c827042a227a94a0a5a12d3209c10a889c252829684b4c827042a226894a0a5a12d3209c10a8898a52829684b4c8270420025694a0a5a12d3209c10a9b94a46829684b4c827042a525291a0a5a12d3209c10a8894a46829684b4c827042 else 0x252829c65f12d3209c1080094a0a7197a4b4c82704200252829c65e52d3209c1080094a0a719754b4c82704200252829c65c92d3209c1080094a0a7196f4b4c82704200252829c65b52d3209c1080094a0a7196c4b4c82704200252829c65a92d3209c1080094a0a719694b4c8270420025291a1a5a12d3209c1080000252831684b4c8270420028898a0a5a12d3209c1080000256829684b4c8270420029b94a0a5a12d3209c10a9ba5252829684b4c827042))) else (if i < 1184 then (if i < 1152 then (if i < 1136 then 0x94a0a7f5c65fd2d3209c10a52829f97197f4b4c82704294a0a7e1c65fd2d3209c10a52829ef7197f4b4c82704294a0a7a1c65fd2d3209c10a52829e57197f4b4c82704294a0a779c65fd2d3209c10a52829c66e57f4b4c82704294a0a719a95fd2d3209c10a52829c66917f4b4c82704294a0a7199c5fd2d3209c10a52829c66517f4b4c82704294a0a719925fd2d3209c10a52829c663d7f4b4c82704294a0a7198e5fd2d3209c1080094a0a7197e4b4c827042 else 0x25291a0a5fd2d3209c10a9494a0a7197f4b4c827042a2252829c65fd2d3209c10a8094a0a7197f4b4c8270429ea52829c65fd2d3209c10a7294a0a7197f4b4c8270429c252829c65fd2d3209c10a6894a0a7197f4b4c82704298a52829c65fd2d3209c10a5291a0a7197f4b4c82704294a3e829c65fd2d3209c10a528f20a7197f4b4c82704294a34829c65fd2d3209c10a5289e0a7197f4b4c82704294a22829c65fd2d3209c10a5286a0a7197f4b4c827042) else (if i < 1168 then 0x94a0a7a1c66712d3209c10a52829e57199c4b4c82704294a0a779c66712d3209c10a52829c66e59c4b4c82704294a0a719a96712d3209c10a52829c669d9c4b4c82704294a0a719a66712d3209c10a52829c66919c4b4c82704200252829c66692d3209c10a52829c6671964b4c8270429c252829c66492d3209c10a52829c6671924b4c8270429c252829c66392d3209c10a52829c66718e4b4c82704200252829c66192d3209c10800a22528297f4b4c827042 else 0x9ea52829c66712d3209c10a7394a0a7199c4b4c8270429c252829c66712d3209c10a6894a0a7199c4b4c82704298a52829c66712d3209c10a5291a0a7199c4b4c82704294a41829c66712d3209c10a528f20a7199c4b4c82704294a34829c66712d3209c10a5289e0a7199c4b4c82704294a22829c66712d3209c10a5286a0a7199c4b4c82704294a0a7f5c66712d3209c10a52829fc7199c4b4c82704294a0a7e1c66712d3209c10a52829ef7199c4b4c827042)) else (if i < 1216 then (if i < 1200 then 0x9a252829c65a1423209c10a528d20a71968508c82704294a0a7bdc65a1423209c1080094a0a719684ecc82704200252829c65a1373209c1080000252829c64d0c82704200252829c65a1343209c1080094a0a719684c4c82704200252829c65a12f3209c1080094a0a719684b8c82704200252829c66912d3209c10800a22528299c4b4c8270420025291a0a6712d3209c10a9494a0a7199c4b4c827042a2252829c66712d3209c10a8094a0a7199c4b4c827042 else 0x94a27829c65a12d3749c10a52829e8719684b4dd2704200252829c65a12d3549c1080094a0a719684b4d02704200252829c65a12d3349c1080094a0a719684b4cb2704200252829c65a12d3289c1080094a0a719684b4c9270420026894a0a7199c3209c1080094a34829c6670c8270429a252829c6671683209c10a528d20a7199c5a0c82704200252829c6661683209c10a52829c666168568c8270429a252829c65a1553209c10a6894a0a71968540c827042) else (if i < 1232 then 0x252829c65a12d320b01080094a0a719684b4c82b84200252829c65a12d320ad1080094a0a719684b4c82ac4200252829c65a12d320a61080094a0a719684b4c828c4200252829c65a12d320a11080094a0a719684b4c82804200252829c65a12d3209e1080094a0a719684b4c82744294a27829c6649684b49c10a5289e0a719685552d27042a0252829c65a12d3b09c10a5289e0a719684b4ec2704200252829c65a12d3a89c10a8094a0a719684b4dd27042 else 0x94a0a7198f5a12d320b110a52829c6639684b4c82c44294a0a7197f5a12d320b110a52829c65a15a4b4c82c44294a0a719685552d320b110a52829c65a1524b4c82c44294a0a719685412d320b110a52829c65a1424b4c82c44294a0a719684b522320b110a52829c65a12d42cc82c44294a0a719684b501320b110a52829c65a12d3e0c82c44294a0a719684b4f4320b110a52829c65a12d3b0c82c44294a0a719684b4dd320b110a52829c65a12d320bd2c442)))) else (if i < 1376 then (if i < 1312 then (if i < 1280 then (if i < 1264 then 0x94a34829c65a12d320b110a5289e0a719684b4c82c44294a24829c65a12d320b110a5288a0a719684b4c82c44294a1a829c65a12d320b110a52829fd719684b4c82c44294a0a7e1c65a12d320b110a52829ef719684b4c82c44294a0a7a1c65a12d320b110a52829e6719684b4c82c44294a0a795c65a12d320b110a52829de719684b4c82c44294a0a719b95a12d320b110a52829c66a5684b4c82c44294a0a7199c5a12d320b110a52829c6649684b4c82c442 else 0x252829c65a12d320ba1080094a0a719684b4c82dc4200252829c66712d320b11080094a0a7197f4b4c82c4420028894a0a5a12d320b11080094a46829684b4c82c442a5252829c65a12d320b110a8894a0a719684b4c82c442a0252829c65a12d320b110a7c94a0a719684b4c82c4429ea52829c65a12d320b110a7094a0a719684b4c82c4429a252829c65a12d320b110a6294a0a719684b4c82c44294a46829c65a12d320b110a528f20a719684b4c82c442) else (if i < 1296 then 0x94a0a719685652d3b0c810a52829c65a1554b4ec3204294a0a719685412d3b0c810a52829c65a1424b4ec3204294a0a719684b5223b0c810a52829c65a12d42cec3204294a0a719684b5013b0c810a52829c65a12d3e0ec3204294a0a719684b4f43b0c81080094a0a719684b4e83204294a0a719684b4ec398c810a52829c65a12d3d0dd3204294a0a719684b4ec374c81080094a0a719684b4d53204294a0a719684b4ec320bd10a52829c65a12d3a0c82f442 else 0x94a1a829c65a12d3b0c810a52829fd719684b4ec3204294a0a7e1c65a12d3b0c810a52829ef719684b4ec3204294a0a7adc65a12d3b0c810a52829e8719684b4ec3204294a0a795c65a12d3b0c810a52829de719684b4ec3204294a0a719b95a12d3b0c810a52829c66a5684b4ec3204294a0a7199c5a12d3b0c810a52829c6655684b4ec3204294a0a719925a12d3b0c810a52829c6639684b4ec3204294a0a7197f5a12d3b0c810a52829c65a15a4b4ec32042)) else (if i < 1344 then (if i < 1328 then 0x28894a0a5a12d3b0c81080094a46829684b4ec32042a5252829c65a12d3b0c810a8894a0a719684b4ec32042a1652829c65a12d3b0c810a8094a0a719684b4ec320429ea52829c65a12d3b0c810a7094a0a719684b4ec320429a252829c65a12d3b0c810a6294a0a719684b4ec3204294a46829c65a12d3b0c810a528f20a719684b4ec3204294a34829c65a12d3b0c810a528ae0a719684b4ec3204294a27829c65a12d3b0c810a5288a0a719684b4ec32042 else 0x98a52829c65a12d320b12700094a0a719684b4c82704a0000094a0a719684b4c81200094a0a719684b4c8270480000094a0a7192d3209c1180094a0a719684b4c82704600252829c65a12d3209c1100094a0a719684b4c8270430028094a0a719684b4ec1080094a27829c65a12d3b0420000094a0a719684b4d510a5288a0a7198e5a12d3204294a22829c65a1504b4c81080094a0a719684b4f43204200252829c66712d3b0c81080094a0a7197f4b4ec32042) else (if i < 1360 then 0x252829c64b4ec1080d0080094a0a5a12d3b04201402002528299c3209c108050080094a0a719683b04200c0200252829c65a12d320480040094a0a7192d3209c1180100252829c65a12d354420040094a0a719343209c1080100252831684b4c8270420040095a0a5a12d3209c108010026294a0a719684b4c82c40094a1a829c65fd2d3209c94a1a829c65fd684b4c82725286a0a719685092d3209c98a52829c65a12d374c827252829c65a1424b4dd3209c else 0x252829c6670ec270420080094a0a7199c3749c1080200252829c6690c82704200800a22528299c3209c108020025291a0a670c8270420080094a0a71d9c3209c108020025282dc6670c8270420080094e0a7199c3209c1080200252829c65a8c8270420080094a0a719343209c1080200252831684b4c8270420080095a0a5a12d3209c1080200252829c65a12d1081f0080094a0a7199c270420700200252829c6670c8108160080094a0a718c82704203802))) else (if i < 1440 then (if i < 1408 then (if i < 1392 then 0x94a0a7199c3b0420080094a0a7199c5a0ec1080200252829c65a1423b0420080094a0a7199c4b4ec1080200252829c65fd2d3b0420080094a0a719694b4ec108020028894a0a5a12d3b0420080094a46829684b4ec1080200252829c75a12d3b0420080094a0b719684b4ec1080200253829c65a12d3b0420080094a0a719684b4d51080200252829c6670ec320420080094a0a7199c320b11080200252829c65a12d2ac420080094a0a7199c3209d10802 else 0x252829c64b4c82704600c0094a0a719684b4d51080300253829c65a0c82704200c0094a0a719343209c1080300252831684b4c82704200c0095a0a5a12d3209c1080300252829c65a09c1081d00c00949c64b4c82704204403002529192d3209c1080d00c0094a0a719684b49c1280200252829c65a12d320480080094a0a7192d3209c1180200252829c65a0c8270440080094a0a719684b4ec10c0200252829c6670c8270430080094a0a719684b4f410802) else (if i < 1424 then 0x252829c65a0c827c420100094a0a719683b09c1080400252829c65a0dd270420100094a0a719683249c1080400252829c65fcc8270420100094a0a7196b3209c108040028894a0a5a0c8270420100094a46829683209c1080400252829c95a0c8270420100094a0b719683209c1080400255829c65a0c8270420100094a0a71968270420700400252829c65a0c8108160100094a0a718c8270420340400252829683209c108050100094a0a719684b4c812003 else 0x2528292d3289c1080d0140094a0a4d0c82704203405002528292e3209c1080d0140094a0c4b4c82704203405002598292d3209c1080d0140095a0a4b4c82704203405002528292d3209c1080d0140094a0a4b4c81081603405002528297f4b4c8270090140094a0a5a12d320b10180500252829c65a0c8270450100000252829c65a0ec108040025289e0a719683b0420100094a0a719684b4ec1080400252829c65a0ec320420100094a0a71968320b110804)) else (if i < 1472 then (if i < 1456 then 0x2528297f4b4c8108160140094a0a5c92d3204205805002528296c4b4c8108160140094a0f5a12d320420580500252831684b4c8108160140095a0a5a12d320420580500252829684b4c8108160140094a0a4b4c82704204405002528292d3209c108100140094a0a4b4c82704203805002528292d3209c1180d0140094a0a4b4ec3204203405002528292d320b11080d0140094a0a4b4c82984203405002528292d320a01080d0140094a0a4b4d02704203405 else 0x2528292d3209c16c420140094a0a5a12d320521080500252829684b4c8120420140094a0a4b4c8270461080500252829684b4c8108360140094a0a4b4c8270420c00500252829684b4c81081f0140094a0a5a12d270420740500252829684b4c8108180140094a0a5a12d3204205c0500252829684b4c8120160140094a0a5a12d354420580500252829684b4ca108160140094a0a5a137320420580500252829684b8c8108160140094a0a6712d3204205805) else (if i < 1488 then 0x25282d684b4c827042014009660a5a12d3209c1080500257829684b4c8270420140095a0a5a12d3209c1080500254829684b4c8270420140094e0a5a12d3209c1080500252829684b4c8270420140094a0a5712d3209c1080500252829344b4c8270420140094a0a4b50d3209c10805002528292d3ecc8270420140094a0a5a12d320921080500252829684b4c81ec420140094a0a5a12d320701080500252829684b4c8190420140094a0a4b4c82706310805 else 0x2528297a4b4c8270420140094a0a5e52d3209c1080500252829754b4c8270420140094a0a5c92d3209c10805002528296f4b4c8270420140094a0a5b52d3209c10805002528316c4b4c8270420140095a0a5b12d3209c10805002528296c4b4c8270420140094a0a5a92d3209c1080500252829694b4c8270420140094a125a12d3209c108050025283d684b4c8270420140094a0d5a12d3209c1080500256831684b4c8270420140094a0c5a12d3209c10805))))) else (if i < 1760 then (if i < 1632 then (if i < 1568 then (if i < 1536 then (if i < 1520 then 0x2528297f4b8c8270420140094a0a5b12e3209c1080500252831684b8c8270420140095a0a5a12e3209c1080500252829684b8c8270420140094a0a6912d3209c10805002528299d4b4c8270420140094a0c6712d3209c10805002568299c4b4c8270420140094a0a6692d3209c1080500252829864b4c8270420140094a0c5fd2d3209c10805002568297f4b4c8270420140094a0a5fd2d3209c10805002528297e4b4c8270420140094a0a5f12d3209c10805 else 0x252831684b4ca270420140095a0a5a12d3289c1080500252829684b4ca270420140094a0a5a12d3249c108050026894a0a670c8270420140094a348299c3209c1080500252829985a0c8270420140094a0a5a13b3209c1080500252829684dcc8270420140000252829343209c1080500252829c64d0c8270420140094a0a5a1343209c1080500252829684c4c8270420140094a0a5a12f3209c10805002528299d4b8c8270420140094a0a6712e3209c10805) else (if i < 1552 then 0x2528297f4b4c8280420140094a0a5b12d320a01080500252831684b4c8280420140095a0a5a12d320a01080500252829684b4c8280420140094a0a5a12d3209e1080500252829684b4c8274420140094a0a5a12d3a89c1080500252829684b4d5270420140094a0a5a12d3409c1080500252829684b4cd270420140094a0a5a12d32c9c1080500252829684b8ca270420140094a0a6712d3289c10805002528297f4b4ca270420140094a0a5b12d3289c10805 else 0x2528299c4b4c82c4420140094a0a5fd2d320b110805002528296c4b4c82c4420140094a0c5a12d320b11080500256829684b4c82c4420140094a0a5a12d320b11080500252829684b4c82c0420140094a0a5a12d320ae1080500252829684b4c82b4420140094a0a5a12d320ab1080500252829684b4c8298420140094a0a5a12d320a31080500252829684b4c8284420140094a0a5a12d328a01080500252829684b8c8280420140094a0a6712d320a010805)) else (if i < 1600 then (if i < 1584 then 0x252829684b4ee328420140094a0a5a12d3b0ca1080500252829684b4f4320420140094a0a5a12d3b8c81080500252829684b8ec320420140094a0a6712d3b0c810805002528297f4b4ec320420140094a0a5b12d3b0c81080500252831684b4ec320420140095a0a5a12d3b0c81080500252829684b4e8320420140094a0a5a12d354c81080500252829684b4c82e8420140094a0a5a12d320b71080500252829684b4ca2c4420140094a0a5a12e320b110805 else 0x25286a0a5fd2d3209c0140094a0a5fd2d374c827005002528297f4b4c82c49c0140094a0a5a12d3209c128050000094a0a5a12d320480140094a0a719684b4c81200500252829684b4c82704801400002528292d3209c1180500252829c64b4c8270460140094a0a5a12d3209c1180500252829684b4c8270440140094a0a5a12d3209c10c050028094a0a5a12d3b0420140094a27829684b4ec108050000094a0a5a12d354420140094a0a719684b4d510805) else (if i < 1616 then 0x252829684b4c8108160200094a0a4b4c8270420340800252829684b4c8270090200094a0a719684b4c81200600252829c64b4c8270460180094a0a719684b4d51080600252829c64d0c8270420180094a0c5a12d3209c1080600256829684b4c82704201800949c64b4c8270420380600252829684b4c82700a01800002528297f4b4c82c40500252829c65fd2d320b10140098a52829684b4c82c405002528297f5a12d320b10140094a0a5a1424b4c82c405 else 0x94a0a5a12d320b10200094a46829684b4c82c40800252829684b4dd3209c0200094a0a5a12d320b12700800252829684b4ec320420200094a0a5a12d320b11080800252829684b4c8288420200094a0a5a12d3309c1080800252829684c0c8270420200094a0a6712d3209c10808002528297f4b4c8270420200094a0a5b92d3209c1080800252831684b4c827042020009620a5a12d3209c1080800252829684b4c8270420200094a0a4b50d3209c10808))) else (if i < 1696 then (if i < 1664 then (if i < 1648 then 0x2528299c4b4c8270420280094a0a5fd2d3209c1080a00252829704b4c8270420280094a0e5a12d3209c1080a00256829684b4c8270420280094a0a5a12d3209c1080a00252829684b4c81ec420280094a0a5a12d320420580a002528292d3209c1080d0280094a0a719684b4c81200900252829c64b4c8270460240094a0a719684b4d51080900252829c64d0c8270420240094a0c5a12d3209c1080900256829684b4c82704202400829c65a12d3204207c09 else 0x25283dc64b4c810816034009660a7192d320420580d00252829c64b4c8108160340094a0a4b4c8270420400d0029b94a0a5a12d3209c0300000252829684b4c82700c00252829684b4c82704203000a22528297f4b4c82700a0000094a0a5fd2d3209c0280094a0a5fd684b4c82700a00252829685092d3209c0280094a0a5a12d3b0c81080a00252829684b4c82c4420280094a0a5a12d320a41080a00252829684b4ce270420280094a0a5a1323209c1080a) else (if i < 1680 then 0x252829c64b4c8120420340094a0a7192d320420d80d00252829c64b4c81081f0340094a0a7192d270420740d00252829c64b4c81081b0340094a0a7192d320420600d00252829c64b4c8120160340094a0a7192d320460580d00252829c64b4d5108160340094a0a7192d340420580d00252829c64dcc8108160340094a0a71934320420580d0028894a0a4b4c8108160340094a468292d320420580d00252829d04b4c8108160340094a0a7312d320420580d else 0x252829c64b4c8270420340094a0a6e92d3209c1080d00252829ab4b4c8270420340094a0c5a12d3209c1080d00256829684b4c8270420340094a0a4b50c3209c1080d002528292d410c8270420340094a0a7192d320921080d002528292d3209c2144203400a22528292d3207b1080d00252829c64b4c81ec420340094a0a4b4c82c47a1080d002528292d3209c1e8420340094a0a7192d320701080d00252829c64b4c8190420340094a0a7192d320521080d)) else (if i < 1728 then (if i < 1712 then 0x259829cc4b4c8270420340094a0a7312d3209c1080d00252829cb4b4c8270420340094a0a7292d3209c1080d00252829c84b4c8270420340094a0a71d2d3209c1080d00252849c64b4c8270420340094a0f7192d3209c1080d00252835c64b4c8270420340094a0c7192d3209c1080d0025282dc64b4c827042034009660a7192d3209c1080d00257829c64b4c8270420340095a0a7192d3209c1080d00254829c64b4c8270420340094e0a7192d3209c1080d else 0x28c9660a4b4c82704203400a22598292d3209c1080d0000095a0a4b4c82704203400a6e528292d3209c1080d0028c94a0a4b4c8270420340095a528292d3209c1080d0025991a0a4b4c8270420340094a468292d3209c1080d0025290e0a4b4c8270420340094a0c8292d3209c1080d00252829f64b4c8270420340094a0a7b92d3209c1080d00252829e74b4c8270420340094a0a78d2d3209c1080d00252829d34b4c8270420340094a0a7412d3209c1080d) else (if i < 1744 then 0x252829c64b4c9270420340094a0a719983209c1080d00252829c64ecc8270420340094a0a719373209c1080d0028894a0a4d0c8270420340094a46829343209c1080d00252829cc4d0c827042034009660a719343209c1080d00252829c64d0c8270420340094a0a719313209c1080d00252829c64bcc8270420340094a0a7192e3209c1080d0025291a274b4c8270420340094a468692d3209c1080d0000094a0c4b4c82704203400a22628292d3209c1080d else 0x252829c64b4c828c420340094a0a7192d320a11080d00252829c64b4c8280420340094a0a7192d3209e1080d00252829c64b4c8274420340094a0a7192d3a89c1080d00252829c64b4d5270420340094a0a719343409c1080d0028894a0a4b4d0270420340094a468292d3409c1080d00252829cc4b4d027042034009660a7192d3409c1080d00252829c64b4d0270420340094a0a7192d3349c1080d00252829c64b4cb270420340094a0a7192d3289c1080d)))) else (if i < 1888 then (if i < 1824 then (if i < 1792 then (if i < 1776 then 0x252829c64d0c82c44203400a22528292d320b11080d0025291a0a4b4c82c4420340094a0a7312d320b11080d00259829c64b4c82c4420340094a0a7192d320b01080d00252829c64b4c82b8420340094a0a7192d320ad1080d00252829c64b4c82ac420340094a0a7192d340a61080d00252829c64d0c82984203400a22528292d320a61080d0025291a0a4b4c8298420340094a0a7312d320a61080d00259829c64b4c8298420340094a0a7192d320a61080d else 0x252829c65a12d354420340094a0a7192d3c4d01080d00252829c64b4ec340420340094a0a7192d3d0c81080d00252829c64b4f1320420340094a0a719343b0c81080d0028894a0a4b4ec320420340094a468292d3b0c81080d00252829cc4b4ec32042034009660a7192d3b0c81080d00252829c64b4e8320420340094a0a7192d354c81080d00252829c64b4c82e8420340094a0a7192d320b71080d00252829c64b4c82d0420340094a0a7192d340b11080d) else (if i < 1808 then 0x252829c64b4ec320460340094a0a7192d320b41180d00252829c64b4c82c4460340094a0a7192d320a61180d00252829c64b4d0270460340094a0a719343209c1180d0028894a0a4b4c8270460340094a468292d3209c1180d00252829cc4b4c827046034009660a7192d3209c1180d00252829c64b4c8270460340094a0a7192d3209c1100d00252829c64b4c82704303400a0252829c64b4ec1080d0025289e0a7192d3b0420340000252829c64b4d51080d else 0x252829c64d0c82704203800002529192d3209c1080e0028894a0a4b4c8270420380094a468292d3209c1080e00252829cd4b4c82704203800a52527192d3209c1080e00252919c64b4c8270420380096a0a7192d3209c1080e00252829c64b4c8270420380094a466712d3209c1080e00252829c64b4c8108160380098a52829c64b4c82c40d00252829c64b4c82704a0340000252829c64b4c81200d00252829c65a12d320480340094a0a7192d3209c1200d)) else (if i < 1856 then (if i < 1840 then 0x252829c64d8c82704204400a22528292d3209c108110025291a0a4b4c8270420440094a0a7392d3209c108110025289dc64b4c827042044009720a7192d3209c1081100252829c64b4c8270420440094a0a4b50c3209c1081100252829c64b4c81081604400002528292d3209c1081000252829c64b4c8270470380094a0a7192d3b0c81080e00252829c64b4c82c4420380094a0a7192d320a71080e00252829c64b4d127042038009a252829c63209c1080e else 0x252829c64b4c818c420580094a0a7192d3205b1081600252829c64b4c8118420580094a0a7192d320420c01600252829c65a12d1081d05800a220a5a12d320420701600252829c64b4c81081b0580094a0a5a12d3204205c1600000949c64b4c8270420480094a0a7192d3209c1081200252719a44b4c8270420480094a0a7192d3209c1181100252829c64b4ec320420440094a0a7192d320b11081100252829c64b4c82a4420440094a0a7192d34c9c10811) else (if i < 1872 then 0x252829c65a12d320420580094a0a6e9684b4c81081600252829ab5a12d320420580094a0a7195c4b4c81081600252829c64d12d320420580094a468292d434c81081600252829c64b50d320420580094a0a5fd2d430c81081600252829684b50c320420580094a0a5a12d410c81081600252829c64b4fb320420580094a0a719343209c1081600252831684b4c8270420580095a0a5a12d3209c1081600252829684b4c8214420580094a0a5a12d3207a10816 else 0x252829d05a12d320420580094a0a731684b4c81081600252829cb5a12d320420580094a0a729684b4c81081600252829c85a12d320420580094a0a71d684b4c81081600252849c65a12d320420580094a0f719684b4c81081600252835c65a12d320420580094a0c719684b4c8108160025282dc65a12d32042058009660a719684b4c81081600257829c65a12d320420580095a0a719684b4c81081600254829c65a12d320420580094e0a719684b4c810816))) else (if i < 1952 then (if i < 1920 then (if i < 1904 then 0x94a0c5a12d3204205800a2268829684b4c8108160028898a0a5a12d320420580000256829684b4c8108160029b94a0a5a12d3204205800a2252829684b4c8108160025694a0a5a12d320420580094a49829684b4c8108160025290e0a5a12d320420580094a0c829684b4c81081600252829f65a12d320420580094a0a7b9684b4c81081600252829e75a12d320420580094a0a78d684b4c81081600252829d35a12d320420580094a0f741684b4c810816 else 0x252829c65e52d320420580094a0a719754b4c8108160028894a0a5c92d320420580094a46829724b4c81081600252829d05c92d320420580094a0f719724b4c81081600252829c65c92d320420580094a0a7196f4b4c81081600252829c65b52d320420580094a0a7196c4b4c81081600252829c65a92d320420580094a0a719694b4c8108160025291a1a5a12d3204205800a225283d684b4c810816002529260f5a12d320420580094a4683d684b4c810816) else (if i < 1936 then 0x252829c66912d320420580094a0a719a04b4c8108160028894a0a6712d320420580094a468299c4b4c81081600252829d06712d320420580094a0f7199c4b4c81081600252829c66692d320420580094a0a719864b4c81081600252829c66092d3204205800a22528297f4b4c8108160025291a0a5fd2d320420580094a0a7417f4b4c8108160025283dc65fd2d320420580094a0a7197e4b4c81081600252829c65f12d320420580094a0a7197a4b4c810816 else 0x252829c666168320420580094a0a719684ecc81081600252829c668137320420580094a0a7199c4dcc81081600252829c65fd37320420580094a0a719724dcc8108160028894a0a5a137320420580094a46829684dcc81081600252829d05a137320420580094a0f719684dcc81081600252829c65a137320420580000252829c64d0c81081600252829c65a134320420580094a0a719684c4c81081600252829c65a12f320420580094a0a719684b8c810816)) else (if i < 1984 then (if i < 1968 then 0x252829c65a137354420580094a0a7199c4b4d51081600252829c65fd2d354420580094a0a719724b4d5108160028894a0a5a12d354420580094a46829684b4d51081600252829d05a12d354420580094a0f719684b4d51081600252829c65a12d354420580094a0a719684b4d01081600252829c65a12d334420580094a0a719684b4cb1081600252829c65a12d328420580094a0a719684b4c9108160026894a0a7199c320420580094a34829c6670c810816 else 0x252829c65a137320480580094a0a7199c4b4c81201600252829c66092d320480580094a0a7197f4b4c81201600252829c65c92d3204805800a2252829684b4c8120160025291a0a5a12d320480580094a0a741684b4c8120160025283dc65a12d320480580094a0a719684b4c8120160000094a0a7192d320460580094a0a719684b4c81181600252829c64b4c8270460580094a0a719684b4c81101600252829c65a12d320430580094a0a719684b4ea10816) else (if i < 2000 then 0x252829c65a139320420600094a0a7199c4b4c81081800252829c65fd2d320420600094a0a719744b4c8108180028894a0a5a12d320420600094a46829684b4c81081800252829d15a12d320420600094a11719684b4c81081800268829c65a12d320420600094a0a719684b4c81081800252829684b4c81e84206000829c65a12d32042070180000094a0a5a12d3204205c0094a1a829c65fd2d3201600252829c65a12d3204a0580094a0a719684b4d512016 else 0x28894a0a5a12d270420740094a46829684b49c1081d00252829d45a12d270420740094a13719684b49c1081d00253829c65a12d270420740094a0a7199c3209c1081d00252829c65a12d320480700094a0a7192d3209c1181c00252829c65a12d354420700094a0b719684b49c1081c00252829c64d0c8270420700094a0c5a12d3209c1081c00256829684b4c8270420700000252829c64b4c81081b00252829c65a12d320480600094a0a719684b4d710818))))))) else (if i < 3024 then (if i < 2512 then (if i < 2256 then (if i < 2128 then (if i < 2064 then (if i < 2032 then 0x252851c65a12d3204207c00a520a719684b4c81081f00288829c65a12d3204207c0094a0a719684b4c81081f00288829684b4ec3204207c0094a0a719684b49c12c1d00252829c65a12d2c4420740094a0a719684b4ac1081d0026894a0a7199c270420740000252829c66709c1081d00252829c667168270420740094a0a719685089c1081d00252829c65a13b270420740094a0a7199c4b49c1081d00252829c65fd2d270420740094a0a719764b49c1081d else (if i < 2048 then 0x252831684b4c8270420900095a0a5a12d3209c1082400252829c65a12d32042084000020a719684b4c8108210020a719684b4f4320420840094a0a719684b4c81301f0025289e0a719684b44207c0094a0a719684b4d51081f00252829c65a13c3204207c0094a0a7199c4b4c81081f00252829c65fd2d3204207c0094a0a719774b4c81081f00000a220a5a12d3204207c00a2252829684b4c81081f0025291a0a5a12d3204207c0094a0a755684b4c81081f else 0x252829c64b4c8270460c00094a0a7192d3b0c81083000252829c64b4c82c4420c00094a0a7192d320af108300025291a1a4b4c8270420c000a22528292d3209c108300025291a0a4b4c8270420c00094a0a719684b4c81202c00252829c65a12d354420b00094a0a719343209c1082c00252831684b4c8270420b00095a0a5a12d3209c1082c00252829c65a12d320480900094a0a7192d3209c1182400252829c65a12d354420900094a0a719343209c10824)) else (if i < 2096 then (if i < 2080 then 0x252829c65a12d354420e40094a0a719343209c1083900252831684b4c8270420e40095a0a5a12d3209c1083900252829c65a12d320480d80094a0a7199c4b4c81083600252829c65fd2d320420d80094a0a7197d4b4c8108360028898a0a5a12d320420d800a2252829684b4c8108360025291a0a5a12d320420d80094a0a7192d3209c1183200252829c65a12d354420c80094a0a719343209c1083200252831684b4c8270420c80095a0a5a12d3209c10832 else 0x25283dc65a12d320481080094a0a719684b4c81204200252829c64b4c8270471080094a0a7192d3b0c81184200252829c64b4c82d0461080094a0a7192d320b11184200252829c64b4c8298461080094a0a7192d3409c1184200252829c64d0c82704610800a22528292d3209c118420025291a0a4b4c8270461080094a0a7312d3209c1184200259829c64b4c8270461080094a0a7192d3209c1184200252829c65a12d320480e40094a0a7192d3209c11839) else (if i < 2112 then 0x25291a0a5a12d320521080094a0a7199c3b0c81404200252829c65a12d3544f1080094a0a719343209c13c4200252831684b4c82704f1080095a0a5a12d3209c13c4200252829c65a12d3204c1080094a0a719684b4d51204200252829c65a137320481080094a0a7199c4b4c81204200252829c66092d320481080094a0a7197f4b4c81204200252829c65c92d3204810800a2252829684b4c8120420025291a0a5a12d320481080094a0a741684b4c812042 else 0x252829c64b4c82c45b1080094a0a7192d3409c16c420028894a0a4b4c82705b1080094a468292d3209c16c4200252829c66712d3b05a1080094a0a719684b4d51644200252829c64d0c8270591080094a0c5a12d3209c1644200256829684b4c8270591080094a0a719684b4c8158420026894a0a7199c320521080094a0a719684dcc81484200252829c66712d320521080094a0a7197f4b4c81484200252829c65ed2d3205210800a2252829684b4c814842))) else (if i < 2192 then (if i < 2160 then (if i < 2144 then 0x252829c65c92d3206410800a2252829684b4c8190420025291a0a5a12d320641080094a0a7192d3b0c818c4200252829c64b4c82c4631080094a0a7192d320a618c420028894a0a4b4c8270631080094a468292d3209c18c4200252829c65a12d354621080094a0a719343209c1884200252831684b4c8270621080095a0a5a12d3209c1884200252829c64b4c8270601080094a27829c64b4ec16c4200252829c64b4ec3205b1080094a0a7192d320b816c42 else 0x252829c64d0c8270791080094a0c5a12d3209c1e44200256829684b4c8270791080094a0a719684b4c81d44200252829c65a12d354701080094a0a7199c4b4c81c04200252829c65fd2d3207010800a2252829684b4c81c0420025291a0a5a12d320701080094a0a719343209c1b84200252831684b4c82706e1080095a0a5a12d3209c1b84200252829c65a12d3206a1080094a0a7192d3209c1a44200252829c66712d320641080094a0a7197f4b4c819042) else (if i < 2176 then 0x28894a0a5fd2d3207b1080094a0a7197f4b4c81ec420028898a0a5a12d3207b10800a6e52829684b4c81ec420028894a0a5a12d3207b1080094a46829684b4c81ec4200252829d05a12d3207b1080094a0a5a12d3d0c81e84200252829684b4ec3207a1080094a0a6712d320b11e842002528297f4b4c82c47a1080094a0a5a12d320b11e84200252829684b4c82807a1080094a0a6712d3209c1e842002528297f4b4c82707a1080094a0a719684b4d51e442 else 0x252829684b4c82ec851080094a0a5a12d320b12144200252829684b4ca270851080094a0a6712d3209c21442002528297f4b4c8270851080094a0a719684b4d520c4200252829c64d0c8270831080094a0c5a12d3209c20c4200256829684b4c82708310800a2252829684b4c82044200252829c65a12d3208110800a2252829684b4c81f0420000094a0a5a12d3207c1080094a0a5a12d320b11f0420028894a0a6712d3207b1080094a0a7199c4b4c81ec42)) else (if i < 2224 then (if i < 2208 then 0x252829684b4c82c49a1080094a0a719684b4c82544200252829c65a12d3ac921080094a0a7199c4b4c82484200252829c65fd2d3209210800a2252829684b4c8248420025291a0a5a12d320921080094a0a791684b4c8248420025283dc65a12d320921080094a0a719684b4d52384200252829c64d0c82708e1080094a0c5a12d3209c2384200256829684b4c82708e10800a2252829684b4c82344200252829684b4f43208c1080094a0a5a12d3b0c821442 else 0x259829c64b4d03209c1080094a0a5a12e328c82704200252831684b4ca3209c1080095a0a5a12d328c82704200252829c6670c82f89c1080094a0a71934320bd2704200252831684b4c82f49c1080095a0a5a12d320bd2704200252829c64d0c82c49c1080094a0c5a12d320b12704200256829684b4c82c49c1080094a0a71934320a62704200259829c64b4c82989c1080094a0c5a12d320a02704200256829684b4c82809c10800a6e52829684b4c826c42) else (if i < 2240 then 0x252829c64d1013209c1080094a0c5a12d404c82704200256829684b5013209c1080094a0a7192d400c82704200252829c64d0fb3209c10800a22528292d3ecc8270420025291a0a4b4fb3209c1080094a0c5a12d3e0c82704200256829684b4f83209c1080094a0a719343b0c82704200252831684b4ec3209c1080095a0a5a12d3b0c82704200252829c64d0dd3209c1080094a0c5a12d374c82704200256829684b4dd3209c1080094a0a71934340c827042 else 0x25291a1a4b50d3209c10800a6e528292d434c8270420028894a0a4b50d3209c1080094a468292d434c82704200252829cc4b50d3209c1080094a0a6912d430c827042002528299c4b50c3209c1080094a0a5fd2d430c827042002528296c4b50c3209c1080094a0a7193442cc82704200252831684b50b3209c1080095a0a5a12d42cc82704200252829684b9043209c1080094a0a6712d410c82704200252829874b5043209c1080094a0a5fd2d410c827042)))) else (if i < 2384 then (if i < 2320 then (if i < 2288 then (if i < 2272 then 0x25291a0a4d12d3209c1080094a0a731344b4c82704200259829c64d12d3209c1080094a0a719344b4c82704200252831684b92d3209c1080095a0a5a12e4b4c82704200252829c64d1223209c1080094a0c5a12d488c82704200256829684b5223209c1080094a468292d45cc82704200252829a44b5163209c1080094a468292d44cc82704200252829c64b5133209c10800002528292d438c8270420025291a0a4b50e3209c1080094a0a5fd2d438c827042 else 0x252831685692d3209c1080095a0a5a15a4b4c82704200252831685552d3209c1080095a0a5a1554b4c82704200252831685412d3209c1080095a0a5a1504b4c8270420025291a0a5292d3209c1080094a0a7194a4b4c82704200252829c65212d3209c1080094a0a719464b4c82704200252829c650d2d3209c1080094a0c5a1424b4c82704200256829685092d3209c1080094a0a7193f4b4c82704200252829c64d92d3209c10800a2252829344b4c827042) else (if i < 2304 then 0x2568299c5a12d3209c1080094a0c649684b4c82704200256829925a12d3209c1080094a0c639684b4c827042002568298e5a12d3209c1080094a0c5fd684b4c827042002568297f5a12d3209c1080094a0c5b1684b4c827042002568296c5a12d3209c10800a6e52829674b4c827042002528297f5992d3209c1080094a0a719614b4c8270420028894a0a5712d3209c1080094a468295c4b4c82704200252829f75712d3209c108009660a7195c4b4c827042 else 0x256829fd5a12d3209c1080094a0c7e1684b4c82704200256829f85a12d3209c1080094a0c7bd684b4c82704200256829ef5a12d3209c1080094a0c7a1684b4c82704200256829e85a12d3209c1080094a0c795684b4c82704200256829e55a12d3209c1080094a0c779684b4c82704200256829de5a12d3209c1080095a0a6e9684b4c82704200252831b95a12d3209c1080094a0c6ad684b4c82704200256829a95a12d3209c1080094a0c671684b4c827042)) else (if i < 2352 then (if i < 2336 then 0x25391a0a5a12d3209c1080094a46829684b4c827042002529160a5a12d3209c1080095a3c829684b4c827042002568d20a5a12d3209c1080094a30829684b4c827042002528ba0a5a12d3209c1080095a27829684b4c8270420025289a0a5a12d3209c1080095a22829684b4c827042002528860a5a12d3209c1080095a1a829684b4c8270420025283a0a5a12d3209c1080095a0c829684b4c827042002528320a5a12d3209c1080094a0c7f5684b4c827042 else 0x27894a0a5a12d3209c108009da52829684b4c8270420026f94a0a5a12d3209c1080099e52829684b4c8270420025894a0a5a12d3209c1080095a52829684b4c827042002529420a5a12d3209c1080094a4e829684b4c8270420025292a0a5a12d3209c1080094a49829684b4c827042002529220a5a12d3209c1080094a47829684b4c8270420025991a0a5a12d3209c1080095e46829684b4c8270420025691a0a5a12d3209c1080095246829684b4c827042) else (if i < 2368 then 0x27095a0a5a12d3209c108009a656829684b4c8270420026895a0a5a12d3209c1080098a56829684b4c8270420000095a0a5a12d3209c10800a2a54829684b4c8270420028994e0a5a12d3209c10800a5652829684b4c8270420029294a0a5a12d3209c10800a4252829684b4c8270420028c94a0a5a12d3209c10800a2e52829684b4c8270420028a94a0a5a12d3209c10800a2652829684b4c8270420028894a0a5a12d3209c10800a1e52829684b4c827042 else 0x25288a0c5a12d3209c1080094a1a831684b4c8270420028894a0b5a12d3209c1080094a4782d684b4c8270420029b98a0a5a12d3209c10800a3259829684b4c827042000009620a5a12d3209c10800a2e57829684b4c8270420029595a0a5a12d3209c10800a5256829684b4c8270420028895a0a5a12d3209c10800a0656829684b4c8270420028095a0a5a12d3209c108009ee56829684b4c8270420027a95a0a5a12d3209c108009c656829684b4c827042))) else (if i < 2448 then (if i < 2416 then (if i < 2400 then 0x28894a0c5a12d3209c10800a0252831684b4c8270420027a94a0c5a12d3209c108009c252831684b4c8270420026894a0c5a12d3209c1080098a52831684b4c8270420025694a0c5a12d3209c1080000252831684b4c8270420025291a0c5a12d3209c1080094a3d831684b4c827042002528f20c5a12d3209c1080094a35831684b4c827042002528d20c5a12d3209c1080094a28831684b4c8270420025289e0c5a12d3209c1080094a23831684b4c827042 else 0x2528320a5b12d3209c10800a22528296a4b4c8270420025291a0a5a92d3209c10800a2252829694b4c8270420025291a0a5a52d3209c10800a6e52869684b4c8270420028894a125a12d3209c1080094a4a849684b4c8270420028894a0f5a12d3209c1080094a4983d684b4c8270420000094a0e5a12d3209c10800a2252835684b4c827042002529220d5a12d3209c1080000256831684b4c8270420029594a0c5a12d3209c10800a5252831684b4c827042) else (if i < 2432 then 0x25291a0a5e92d3209c10800a2252829794b4c8270420025291a0a5e52d3209c10800a2252829754b4c8270420025291a0a5d52d3209c10800a2252829724b4c8270420025291a0a5c92d3209c10800a22528296f4b4c8270420025291a0a5bd2d3209c10800a22528296d4b4c8270420025291a0a5b52d3209c10800002528316c4b4c8270420000095a0a5b12d3209c10800a22528296c4b4c8270420025694a0a5b12d3209c1080094a468296c4b4c827042 else 0x252835c65fd2d3209c1080094a0c7197f4b4c8270420025282dc65fd2d3209c108009660a7197f4b4c82704200257829c65fd2d3209c1080095a0a7197f4b4c82704200254829c65fd2d3209c1080094e0a7197f4b4c82704200252829c65fd2d3209c1080094a0a6e97f4b4c82704200252829ab5fd2d3209c10800a22528297e4b4c8270420025291a0a5f92d3209c10800a22528297c4b4c8270420025291a0a5f12d3209c10800a22528297a4b4c827042)) else (if i < 2480 then (if i < 2464 then 0x25290e0a5fd2d3209c1080094a308297f4b4c827042002528320a5fd2d3209c1080094a0a7d97f4b4c82704200252829ee5fd2d3209c1080094a0a79d7f4b4c82704200252829e35fd2d3209c1080094a0a74d7f4b4c82704200252829d05fd2d3209c1080094a0a7317f4b4c82704200252829cb5fd2d3209c1080094a0a7297f4b4c82704200252829c85fd2d3209c1080094a0a71d7f4b4c82704200252849c65fd2d3209c1080094a0f7197f4b4c827042 else 0x259829c66392d3209c1080094a0a719884b4c8270420028894a0a6192d3209c1080094a46829864b4c82704200252829c66152d3209c1080094a0a719834b4c82704200252829c66092d3209c1080094a0a719814b4c82704200252829c66012d3209c1080094a468697f4b4c8270420000094a0c5fd2d3209c10800a22628297f4b4c8270420000095a0a5fd2d3209c10800a6e528297f4b4c8270420026f94a0a5fd2d3209c1080095a528297f4b4c827042) else (if i < 2496 then 0x252831c66712d3209c1080094a0b7199c4b4c82704200259829c66712d3209c1080095e0a7199c4b4c82704200256829c66712d3209c108009520a7199c4b4c82704200253829c66712d3209c1080094a0a7199c4b4c82704200252829ba6712d3209c1080094a0a6ad9c4b4c82704200252829c666d2d3209c10800a22528299a4b4c8270420025291a0a6692d3209c1080094a0a719994b4c82704200252829c665d2d3209c108009660a719924b4c827042 else 0x25290e0a6712d3209c1080094a0c8299c4b4c82704200252829f66712d3209c1080094a0a7b99c4b4c82704200252829e76712d3209c1080094a0a78d9c4b4c82704200252829d36712d3209c1080094a0a7419c4b4c82704200252829cc6712d3209c1080094a0a72d9c4b4c82704200252829ca6712d3209c1080094a0a7219c4b4c82704200252829c76712d3209c1080094a127199c4b4c8270420025283dc66712d3209c1080094a0d7199c4b4c827042))))) else (if i < 2768 then (if i < 2640 then (if i < 2576 then (if i < 2544 then (if i < 2528 then 0x252829e85a12e3209c10800a2252829a44b4c8270420025291a0a6912d3209c1080094a0a719a34b4c82704200252829c66892d3209c1080094a0a719a14b4c82704200252829c66812d3209c1080094a0a7199f4b4c82704200252829c66792d3209c1080094a0a7199d4b4c8270420025291a1a6712d3209c10800002528319c4b4c8270420028898a0a6712d3209c10800002568299c4b4c8270420029b94a0a6712d3209c1080095a528299c4b4c827042 else 0x252829c667d313209c1080094a0a7197f4c4c8270420028894a0a5a1313209c1080094a46829684c4c82704200252829c66792f3209c1080094a0a7197f4bcc8270420028894a0a5a12f3209c1080094a46829684bcc82704200252829c66752e3209c1080094a0a7197f4b8c8270420000094a0c5a12e3209c1080000256829684b8c8270420028894a0a5a12e3209c1080095a52829684b8c8270420025291a0a5a12e3209c1080094a0c829684b8c827042) else (if i < 2560 then 0x252829cc719343209c1080094a0a719b94d0c82704200252829c66a5343209c1080094a0a7199c4d0c82704200252829c6649343209c1080094a0a7198e4d0c82704200252829c65fd343209c10800a2252829684d0c8270420025291a0a5a1343209c1080094a0a7195a4d0c82704200252829c6559343209c1080094a0a719554d0c82704200252829c6545343209c1080094a0a719504d0c82704200252829c650d343209c1080094a0a719424d0c827042 else 0x26294a0a719343209c1080096652829c64d0c8270420000094a0a719343209c1080094a46829c64d0c827042002528f20a719343209c1080094a34829c64d0c8270420025289e0a719343209c1080094a22829c64d0c8270420025286a0a719343209c1080094a0a7f5c64d0c82704200252829f8719343209c1080094a0a7c1c64d0c82704200252829ef719343209c1080094a0a7a1c64d0c82704200252829e5719343209c1080094a0a779c64d0c827042)) else (if i < 2608 then (if i < 2592 then 0x252829c6681373209c1080094a0a7197f4dcc8270420028894a0a5a1373209c1080094a46829684dcc8270420000094a0a719363209c108000028894a0a4d0c8270420000094a46829343209c1080000252829cc4d0c827042000009660a719343209c10800a5252829c64d0c8270420028894a0a719343209c10800a0252829c64d0c8270420027a94a0a719343209c108009c252829c64d0c8270420026a94a0a719343209c108009a252829c64d0c827042 else 0x94a0a719993209c1080094a0a7199c660c82704200252829c66617f3209c108009a252829c65a8c8270420025282dc6671683209c1080094e0a7199c5a0c8270420028894a0a661683209c1080094a46829985a0c82704200252829c66655c3209c1080094a0a71d68508c8270420025282dc65a1423209c1080094e0a71968508c82704200252829c66853b3209c1080094a0a7197f4ecc8270420028894a0a5a13b3209c1080094a46829684ecc827042) else (if i < 2624 then 0x28894a0a5a12d3249c1080094a46829684b4c9270420026894a0a719a43209c1080094a34829c6690c827042002889a2528299c3209c108009a25291a0a670c8270420028894a348299c3209c1080094a468d20a670c827042002528d2277199c3209c108000025282dc6670c827042002949a20a7199c3209c10800a0268829c6670c8270420000094e0a7199c3209c10800a5e52829c6670c8270420025394a0a7199c3209c1080094a0b829c6670c827042 else 0x28894a0a5a12d32c9c1080094a46829684b4cb270420000094a0a5a12e3289c1080094a0a7199c4b4ca2704200252829c65fd2d3289c1080000252831684b4ca270420000095a0a5a12d3289c10800a2252829684b4ca270420025694a0a5a12d3289c1080094a46829684b4ca27042002528320a5a12d3289c1080094a0a7bd684b4ca2704200252829684b92d3289c108009a252829c65a0c92704200252829c66712d3249c1080094a0a7197f4b4c927042))) else (if i < 2704 then (if i < 2672 then (if i < 2656 then 0x25291a0a5a12d3549c1080000252829c64d0d027042000009660a7192d3409c108009c252829c64b4d0270420025994a0a7192d3409c1080094a0a7199c4b4d02704200252829c65fd2d3409c10800a2252829684b4d0270420025291a0a5a12d3409c1080094a0a719344b4d02704200252829c66712d3349c1080094a0a7197f4b4cd270420028894a0a5a12d3349c1080094a46829684b4cd2704200252829c66712d32c9c1080094a0a7197f4b4cb27042 else 0x28894a0a5a12d3209d1080094a46829684b4c8274420025289e0a719684ec9c1080094a27829c65d52d270420025282dc65a12d3b09c1080094e0a719684b4ec2704200252829c66712d3a89c1080094a0a7197f4b4ea270420028894a0a5a12d3a89c1080094a46829684b4ea2704200252829c75a12d3749c1080094a0b719684b4dd2704200253829c65a12d3749c1080094a0a7199c4b4d52704200252829c65fd2d3549c10800a2252829684b4d527042) else (if i < 2688 then 0x25291a0a5a12d320a11080094a0a7199c4b4c82804200252829c65fd2d320a01080000252831684b4c8280420000095a0a5a12d320a010800a2252829684b4c8280420025694a0a5a12d320a01080094a46829684b4c828042002528320a5a12d320a0108009a252829c65a0c82784200252829c66712d3209e1080094a0a7197f4b4c8278420028894a0a5a12d3209e1080094a46829684b4c82784200252829c66712d3209d1080094a0a7197f4b4c827442 else 0x94a0a71934320a61080000259829c64b4c8298420027094a0a7192d320a61080096652829c64b4c82984200252829c66712d320a61080094a0a7197f4b4c8298420028894a0a5a12d320a61080094a46829684b4c82984200252829c64d12d320a61080094a0a7199c4b4c828c4200252829c65fd2d320a310800a2252829684b4c828c420025291a0a5a12d320a31080094a0a7199c4b4c82844200252829c65fd2d320a110800a2252829684b4c828442)) else (if i < 2736 then (if i < 2720 then 0x252829c65fd2d320b010800a2252829684b4c82c0420025291a0a5a12d320b01080094a0a7199c4b4c82b84200252829c65fd2d320ae10800a2252829684b4c82b8420025291a0a5a12d320ae1080094a0a7199c4b4c82b44200252829c65fd2d320ad10800a2252829684b4c82b4420025291a0a5a12d320ad1080094a27829c65a12d2ac4200252829c66712d320ab1080094a0a7197f4b4c82ac420028894a0a5a12d320ab1080094a46829684b4c82ac42 else 0x257829c65a12d320b11080095a0a719684b4c82c44200254829c65a12d320b11080094e0a719684b4c82c44200252829c65a12d320b11080094a0a6e9684b4c82c44200252829ab5a12d320b11080094a0a7195c4b4c82c44200252829c64d12d320b11080094a468292d434c82c44200252829c64b50d320b11080094a0a5fd2d430c82c44200252829684b50c320b11080094a0a5a12d410c82c44200252829c64b4fb320b11080094a0a7199c4b4c82c042) else (if i < 2752 then 0x252829ee5a12d320b11080094a0a79d684b4c82c44200252829e35a12d320b11080094a0a74d684b4c82c44200252829d05a12d320b11080094a0a731684b4c82c44200252829cb5a12d320b11080094a0a729684b4c82c44200252829c85a12d320b11080094a0a71d684b4c82c44200252849c65a12d320b11080094a0f719684b4c82c44200252835c65a12d320b11080094a0c719684b4c82c4420025282dc65a12d320b1108009660a719684b4c82c442 else 0x252829c65bd2d320b11080094a0a7196d4b4c82c44200252829c65b12d320b11080094a0a7196a4b4c82c44200252829c65a52d320b11080094a46869684b4c82c4420000094a0c5a12d320b110800a2262829684b4c82c4420000095a0a5a12d320b110800a6e52829684b4c82c4420027694a0a5a12d320b11080095a52829684b4c82c4420025290e0a5a12d320b11080094a21829684b4c82c442002528320a5a12d320b11080094a0a7d9684b4c82c442)))) else (if i < 2896 then (if i < 2832 then (if i < 2800 then (if i < 2784 then 0x252829c65a131320b11080094a0a719684bcc82c44200252829c65a12e320b11080094a0a719a44b4c82c4420028894a0a6712d320b11080094a468299c4b4c82c44200252829c66692d320b11080094a0a719864b4c82c4420028894a0a5fd2d320b11080094a468297f4b4c82c44200252829c65f92d320b11080094a0a7197c4b4c82c44200252829c65e92d320b11080094a0a719794b4c82c44200252829c65d52d320b11080094a0a719724b4c82c442 else 0x252829c65a12d320b31080094a0a719684b4c82c84200252829c65a12d3a8b11080094a0a719684b4d52c44200252829c65a12d340b11080094a0a719684b4cd2c44200252829c65a12d32cb11080094a0a719684b4ca2c44200252829c65a12d324b1108009a252829c6670c82c442002528d20a7199c320b11080094a0a719985a0c82c44200252829c65a13b320b11080094a0a719684dcc82c4420000094a0a71934320b11080094a0a719684d0c82c442) else (if i < 2816 then 0x252829d05a12d354c81080094a0f719684b4d53204200252829c65a12d354c81080094a0a719684b4d52f44200252829c65a12d320bc1080094a0a7199c4b4c82e84200252829c65fd2d320ba10800a2252829684b4c82e8420025291a0a5a12d320ba1080094a0a719684b4c82e44200252829c66712d320b71080094a0a7197f4b4c82dc420028894a0a5a12d320b71080094a46829684b4c82dc4200252829c65a12d320b61080094a0a719684b4c82d042 else 0x28894a0a5a12d3a0c81080094a46829684b4e83204200252829c65a12d39cc810800a2252829684b4e53204200252829c65a12d394c81080094a0a719684b4e33204200252829c65a12d384c81080094a0a719684b4df3204200252829c65a12d370c81080094a0a719684b4d73204200252829c65a137354c81080094a0a7199c4b4d53204200252829c65fd2d354c81080094a0a719724b4d5320420028894a0a5a12d354c81080094a46829684b4d532042)) else (if i < 2864 then (if i < 2848 then 0x253829c65a12d3b0c81080094a0a719684b4ec3204200252829ba5a12d3b0c81080094a0a6ad684b4ec3204200252829c65712d3b0c81080094a0a719344b4ec320420025291a0a4b50d3b0c81080094a0a7192d434ec32042002528297f4b50c3b0c81080094a0a5a12d430ec3204200252829684b5043b0c81080094a0a7192d3ecec3204200252829c65a12d3acc81080094a0a719684b4e93204200252829c66712d3a0c81080094a0a7197f4b4e832042 else 0x252829d35a12d3b0c81080094a0a741684b4ec3204200252829cc5a12d3b0c81080094a0a72d684b4ec3204200252829ca5a12d3b0c81080094a0a721684b4ec3204200252829c75a12d3b0c81080094a12719684b4ec320420025283dc65a12d3b0c81080094a0d719684b4ec3204200252831c65a12d3b0c81080094a0b719684b4ec3204200259829c65a12d3b0c81080095e0a719684b4ec3204200256829c65a12d3b0c8108009520a719684b4ec32042) else (if i < 2880 then 0x252829c65b52d3b0c81080094a0a7196c4b4ec3204200252829c65a92d3b0c81080094a0a719694b4ec320420025291a1a5a12d3b0c81080000252831684b4ec320420028898a0a5a12d3b0c81080000256829684b4ec320420029b94a0a5a12d3b0c81080095a52829684b4ec320420025290e0a5a12d3b0c81080094a0c829684b4ec3204200252829f65a12d3b0c81080094a0a7b9684b4ec3204200252829e75a12d3b0c81080094a0a78d684b4ec32042 else 0x252829c65a12f3b0c81080094a0a719684b8ec3204200252829c66912d3b0c810800a22528299c4b4ec320420025291a0a6712d3b0c81080094a0a7199a4b4ec3204200252829c66192d3b0c810800a22528297f4b4ec320420025291a0a5fd2d3b0c81080094a0a7197e4b4ec3204200252829c65f12d3b0c81080094a0a7197a4b4ec3204200252829c65e52d3b0c81080094a0a719754b4ec3204200252829c65c92d3b0c81080094a0a7196f4b4ec32042))) else (if i < 2960 then (if i < 2928 then (if i < 2912 then 0x25291a0a5a12d3d0c81080094a0a719684b4f33204200252829c65a12d3c8c81080094a0a719684b4f13204200252829c65a12d3c0c81080094a0a719684b4ef3204200252829c65a12d3b8c81080094a0a719684b4ed320420026894a0a7199c3b0c81080094a34829c6670ec3204200252829c6661683b0c81080094a0a719684ecec3204200252829c65a1373b0c81080000252829c64d0ec3204200252829c65a1343b0c81080094a0a719684c4ec32042 else 0x252829c65a12d3bccb1080094a0a719684b4ee3284200252829c65a12d3b4c9108000025283dc65a137320420025288a0a719684dcc81080094a0f829c65a137320420000094a0f719724b4c81080094a22829c65c92d320420025283e0a719724b4c81080094a0f7198e5a12d320420025283dc65c9684b4c81080094a0f719685412d320420025283dc65a1374b4c81080094a0a7199c4b4f43204200252829c65fd2d3d0c810800a2252829684b4f432042) else (if i < 2944 then 0x252829c65c9684b4d51080094a0a719685692d3544200252829c65a1574b4d51080094a0a719685552d3544200252829c65a1504b4d51080094a0a719685092d3544200252829c65a1374b4d51080094a0a719684b5223544200252829c65a12d42cd51080094a0a719684b5013544200252829c65a12d3e0d51080094a0a719684b4ec3544200252829c65a12d37cd51080094a0a719684b4dd3544200252829c65a12d3c4d01080094a0a719684b4f033442 else 0x25283e0a719684b4d51080094a0a7f5c65a12d3544200252829f8719684b4d51080094a0a7bdc65a12d3544200252829e9719684b4d51080094a0a7a1c65a12d3544200252829e5719684b4d51080094a0a779c65a12d3544200252829d0719684b4d51080094a0a719b95a12d3544200252829c66a5684b4d51080094a0a7199c5a12d3544200252829c664d684b4d51080094a0a719925a12d3544200252829c6639684b4d51080094a0a7197f5a12d35442)) else (if i < 2992 then (if i < 2976 then 0x94a0f719684b4d510800a5252829c65a12d354420028894a0a719684b4d510800a0252829c65a12d354420027a94a0a719684b4d5108009c252829c65a12d354420026894a0a719684b4d51080098a52829c65a12d354420000094a0a719684b4d51080094a46829c65a12d35442002528f20a719684b4d51080094a34829c65a12d35442002528a60a719684b4d51080094a27829c65a12d354420025288a0a719684b4d51080094a1a829c65a12d35442 else 0x2809a20a719684b4ec1080000253829c65a12d3b0420029a94a0a719684b4ec1080094e52829c65a12d3b0420025282e0a719684b4ec1080094a0a719684b5233b0420000094a0a719684b4eb1080094a0a719684b4ec3a8420000094a0a719684b4d71080000252829c65a137354420000094a0a7199c4b4d51080000252829c65fd2d354420000094a0a719724b4d5108000028894a0a5a12d354420000094a46829684b4d51080000252829d05a12d35442) else (if i < 3008 then 0x252829c66012d3209c10c00a2252829684b4c8270430025291a0a5a12d3209c10c00a0252829c65a12d3d0420025289e0a719684b4f410800a0252829c66712d3b0420025289e0a7199c4b4ec10800a0252829c65fd2d3b0420025289e0a7197f4b4ec10800a228094a0a5a12d3b0420028094a46829684b4ec10800a225289e0a5a12d3b0420025291a27829684b4ec10800a525289dc65a12d3b042002528d227719684b4ec108000025282dc65a12d3b042 else 0x252829c64b4c8270831180094a0a7192d3209c1e44600252829c64b4c82706e1180094a0a7192d3209c1884600252829c64b4c8270591180094a0a7192d3209c13c4600252829c65a12d3b0c81100094a0a719684b4c82cc440026894a0a719683209c1100094a0a7199c4b4c82704400252829c66052d3209c11000a2252829684b4c8270440025291a0a5a12d3209c1100094a0a719684b4ec3204300252829c65a12d320b210c0094a0a7199c4b4c827043)))))) else (if i < 3520 then (if i < 3264 then (if i < 3136 then (if i < 3072 then (if i < 3040 then 0x252829c650d2d3209c1180094a0a719424b4c82704600252829c64d12d3209c1180094a0a7192d488c82704600252829c64b50b3209c1180094a0a7192d404c82704600252829c64b4f83209c1180094a0a7192d3b0c82704600252829c64b4de3209c1180094a0a7192d374c82704600252829c64b4d03209c1180094a0a7192d320bd2704600252829c64b4c82d09c1180094a0a7192d320b12704600252829c64b4c82989c1180094a0a7192d3209c23846 else (if i < 3056 then 0x252829e87192d3209c1180094a0a795c64b4c82704600252829df7192d3209c1180094a0a779c64b4c82704600252829cc7192d3209c1180094a0a719b94b4c82704600252829c66a52d3209c1180094a0a7199c4b4c82704600252829c66492d3209c1180094a0a7198e4b4c82704600252829c65fd2d3209c11800a2252829684b4c8270460025291a0a5a12d3209c1180094a0a7195a4b4c82704600252829c65552d3209c1180094a0a719504b4c827046 else 0x27a94a0a7192d3209c118009c252829c64b4c8270460026894a0a7192d3209c1180098e52829c64b4c8270460026294a0a7192d3209c1180096652829c64b4c8270460000094a0a7192d3209c1180094a46829c64b4c827046002528f20a7192d3209c1180094a34829c64b4c8270460025289e0a7192d3209c1180094a22829c64b4c8270460025286a0a7192d3209c1180094a0a7f5c64b4c82704600252829f87192d3209c1180094a0a7bdc64b4c827046)) else (if i < 3104 then (if i < 3088 then 0x94a0a7192d3209c11c0000252829c64b4ec3204600252829c65a12d3b0c81180000252829c64b4c82d04600252829c65a12d320b41180000252829c64b4c82c4460000094a0a7192d320a61180000252829c64b4d0270460000094a0a719343209c118000028894a0a4b4c8270460000094a468292d3209c1180000252829cc4b4c827046000009660a7192d3209c11800a5252829c64b4c8270460028894a0a7192d3209c11800a0252829c64b4c827046 else 0x252829c65a12d37cc81200094a0a719684b4dd3204800252829c65a12d354c81200094a0a719684b4c82f44800252829c65a12d320b11200094a0a7199c4b4c82704800252829c66092d3209c12000a2252829684b4c8270480025291a0a5a12d3209c1200094a0a719684b4c82384800252829c65a12d320831200094a0a719684b4c81e44800252829c65a12d3206e1200094a0a719684b4c81884800252829c65a12d320591200094a0a719684b4c813c48) else (if i < 3120 then 0x252829c6649684b4c81200094a0a7198e5a12d3204800252829c6609684b4c81200094a0a7197f5a12d3204800252829c65c9684b4c81200094a0a719685692d3204800252829c65a1554b4c81200094a0a719685412d3204800252829c65a1444b4c81200094a0a719685092d3204800252829c65a1374b4c81200094a0a719684b5223204800252829c65a12d42cc81200094a0a719684b5013204800252829c65a12d3e0c81200094a0a719684b4ec32048 else 0x25289e0a719684b4c81200094a22829c65a12d320480025286e0a719684b4c81200094a1a829c65a12d320480025283e0a719684b4c81200094a0a7f5c65a12d3204800252829f8719684b4c81200094a0a7bdc65a12d3204800252829e8719684b4c81200094a0a795c65a12d3204800252829e0719684b4c81200094a0a779c65a12d3204800252829d0719684b4c81200094a0a719b95a12d3204800252829c66a5684b4c81200094a0a7199c5a12d32048))) else (if i < 3200 then (if i < 3168 then (if i < 3152 then 0x94a0a719724b4c8120000028894a0a5a12d320480000094a46829684b4c81200000252829d05a12d320480000094a0f719684b4c812000a5252829c65a12d320480028894a0a719684b4c812000a0252829c65a12d320480027a94a0a719684b4c8120009c252829c65a12d320480026894a0a719684b4c81200098a52829c65a12d320480000094a0a719684b4c81200094a46829c65a12d32048002528f20a719684b4c81200094a34829c65a12d32048 else 0x28898a0a5a12d374c827000a2262829684b4c82c49c0026294a0a5a12d320b11e80000252829c65a12d3204c00252829c65a12d3b0c81280094a0a719684b4c82d84a0025289e0a719684b49c1280094a0a7199c4b4c82704a00252829c660d2d3209c12800a2252829684b4c82704a0025291a0a5a12d3209c1280000252829c65a12d354480000094a0a719684dcc81200000252829c66712d320480000094a0a719824b4c81200000252829c65fd2d32048) else (if i < 3184 then 0xa2262829684b4c82c400a226294a0a5a12d320b10026294a46829684b4c82c400a5262829c65a12d320b10028898a0a719684b4c82c40098a52829ba5a12d320b10025286a0a719a44b4c8270000025291a1a5fd2d3209c0028894a1a8297f4b4c82700094a4686a0a5fd2d3209c0029494a1a7197f4b4c82700094a46869c65fd2d3209c0025286a0a6ad7f4b4c82700094a468697f5a12d3209c0025291a1a5a1424b4c82700094a1a8297f4b50c3209c else 0x95a0a5a12d3b0420080000252829c6670d5108020000094a0c670c82704200800002568299c3209c1080200000829c65a12d108210080000252829c66704207c0200000a220a5a12d1081f0080000252718c827042048020000094a0a718ec1080e0080000252918c827042038020000094a0a670ec108050080098a52829c65a12d3d0c80025286a0a7197f4b4ec3200098a52829c66712d320b10026294a0a7197f4b4c82c40094a1a829c65fd2d320b1)) else (if i < 3232 then (if i < 3216 then 0x94a464b4c82704600c0000253829c65a0ec108030000094a0a719684b44c0080000252829c6670c8120020000094a0a718c8270470080000252829c64b4ec118020000094a0a7199c3b0430080000252829c6670f4108020000094a0a719a43b042008000028894a0a670ec108020000094a468299c3b0420080000252829c7670ec108020000094a0b7199c3b0420080000253829c6670ec108020000094a0a719343b0420080000252831684b4ec10802 else 0x94a0a4b4c82c41101400002528292d32048034050000094a0a4b4d51080d0140000252829c65a0ec114040000094a0a719683d0420100000252829c65a0ed108040000094a0a7197f3b0420100000252829c65acec1080400000a2252829683b042010000025291a0a5a0ec108040000094a0a725683b042010000025282dc65a0ec10804000009560a719683b0420100000252829c65a04207c040000094a0a718ec1080d0100000252829683b04201404) else (if i < 3248 then 0x94a0b670c82704201400002538299c3209c108050000094a0a664c8270420140000252829363209c108050000094a0a4d4c8270420140000252831343209c10805000009660a4d0c8270420140000256829343209c108050000094a0a4d0c827042014000020a5a12d32042084050000094a0a6709c1081d01400002528292d3204206c050000094a0a5fd2d3201801400002528292d32046058050000094a0a4d0c81081601400002524b4c82704204805 else 0x94a0a5c92d3544201400002528296c4b4d5108050000094a0f5a12d354420140000252831684b4d5108050000095a0a5a12d354420140000252829684b4d5108050000094a0f5a13732042014000025283d724b4c8108050000094a0a4d0ec32042014000025282934320b1108050000094a0a4d0c82984201400002598292d320a6108050000094a0a4d0c8280420140000252829343409c10805000009660a4b4d0270420140000252829343289c10805)))) else (if i < 3392 then (if i < 3328 then (if i < 3296 then (if i < 3280 then 0x94a0a4b4ca270460140000252829343209c118050000094a0a4b8c82704601400002528312d3209c11805000009660a4b4c82704601400002568292d3209c118050000094a0a4b4c827046014000025282d684b4ec108050000094e0a5a12d3b0420140000252829684b4eb108050000094a0a5a12d35c420140000252829684b4d6108050000094a0a5a137354420140000252829684b8d5108050000094a0a6712d3544201400002528297f4b4d510805 else 0x94a0a6712d320480140000252829824b4c8120050000094a0a5fd2d320480140000252829724b4c8120050000094a0a5b12d32048014000025283d684b4c8120050000094a0c5a12d320480140000256829684b4c8120050000094a0a5a12d3204801400002528292d3209c11c050000094a0a4b4ec3204601400002528292d320b4118050000094a0a4b4c82c44601400002528292d320a6118050000094a0a4b4c82804601400002528292d3409c11805) else (if i < 3312 then 0x94a0a4d0c8270420200000252829684b4c806008000009492d3209c1080e02000002528292d320b1034080000095a0a5a12d320b101800002528297f4b4f4320050000094a0a5fd2d328b101400002528297f4b8c82c4050000094a0a6912d320b101400002528317f4b4c82c4050000095a0a5fd2d320b10140000252829684b4c8130050000094a0a5a12d354480140000252829684b4ca120050000094a0a5a137320480140000252829684b8c812005 else 0x94a0a4b4c8270460280000252829684b4d51080a0000094a0a4d0c827042028000020a5a12d3204207c0a0000094a0a5fd2d3201602800002528292d3209c0440a0000094a0c5fd2d3209c0240000252829684b4f4320080000094a0a5a12d330b10200000252829684c0c82c4080000094a0a6712d320b102000002528296e4b4c82c4080000094a0c5a12d320b10200000258829684b4c82c4080000094a0a5a12d320480200000252829684b4d510808)) else (if i < 3360 then (if i < 3344 then 0x94a0a5a12d320a50300000252829684b4cf2700c0000094a0a5a1333209c03000002528299c4b4c82700c0000094a0a5c52d3209c0300000252839684b4c82700c000009620a5a12d3209c0300000252829684b4c80580c0000094a0a4b4c82700d03000002528297f4b4ec3200a0000094a0a5fd2d320a402800002528297f4b4ce2700a0000094a0a5fd323209c0280000252829a44b4c82700a0000094a0e5fd2d3209c02800002568297f4b4c82700a else 0x94a0c4b8c82704203400002568292e3209c1080d0000094a0e4b4c82704203400002598312d3209c1080d0000095a0c4b4c82704203400002528312d3209c1080d0000096e0a4b4c82704203400002588292d3209c1080d0000095a0a4b4c82704203400002528292d3207c1080d00000829c64b4c81082103400002888292d3204207c0d0000094a0a4b4c81081703400002528312d320420580d0000095a0a4b4c8108160340000252829684b4ec3200c) else (if i < 3376 then 0x94a0f719373204203400002528312d3b0c81080d0000095a0a4b4ec3204203400002528312d320b11080d0000095a0a4b4c82c44203400002528312d320a61080d0000095a0a4b4c82984203400002528312d320a01080d0000095a0a4b4c82804203400002528312d3409c1080d0000095a0a4b4d02704203400002528292e3289c1080d0000094a0c4b4ca2704203400002568292d3289c1080d0000094a0c4d0c8270420340000256829343209c1080d else 0x94a0c4b4c82704603400002568292d3209c1180d0000094a0b7192d3b0420340000253829c64b4ec1080d0000094a0a7192d3ac420340000252829c64b4d81080d0000094a0a7192d35c420340000252829c64dcd51080d0000094a0a7193435442034000028894a0a4b4d51080d0000094a468292d354420340000252829d04b4d51080d0000094a0a7312d35442034000025283dc64b4d51080d000009660a7192d354420340000252829c64b4d51080d))) else (if i < 3456 then (if i < 3424 then (if i < 3408 then 0x94a464b4c810816038000028898a0a4b4c82c40d0000094a0a7192d3204c0340000252829c64b4c81240d0000094a0a7192d354480340000252829c64b4d01200d0000094a0a71937320480340000252829c64d0c81200d00000a22528292d32048034000025291a0a4b4c81200d0000094a0a7412d320480340000252829cc4b4c81200d0000094a0f7192d320480340000259829c64b4c81200d0000094a0a7192d320480340000252829c64b4d51180d else 0x94a0a7192d3204803800002529192d3209c11c0e0000094a0a7192d3544203800002529192d3b0c81080e0000094a464b4c82c44203800002529192d320a71080e0000094a464b4d127042038000026894a463209c1080e00000a5268718c8270420380000253829c63209c1080e0000094a464d0c827042038000029b9492d3209c1080e0000096a464b4c82704203800002528312d3209c1080e0000095a0a4b4c8270420380000252829c6270420740e) else (if i < 3440 then 0x949cf4b4c827042048000025d7192d3209c1081200000949c64b4c8108160480000252829c64b4c8120110000094a0a7192d3544204400002568292d3209c108110000094a0a4b4c82704604000002528292d3b0c8108100000094a0a4b4c82c44204000002528292d320a8108100000094a0a4b4d2270420400000252829353209c108100000094a0c4b4c827042040000025b8292d3209c108100000094a0a4b4c810816040000025282dc63209c1080f else 0x95a0c5a12d320420580000252831684b4c810816000009620a5a12d320420580000256829684b4c8108160000094a0a4b50e320420580000252829c667042074160000094a0a4b4c82704604c00002528312d3209c1081300000949c64b4c82704704800002527192d3b0c81081200000949c64b4c82c44204800002527192d320aa1081200000949c64b4d4270420480000268949c63209c1081200000949c64d8c82704204800002889492d3209c10812)) else (if i < 3488 then (if i < 3472 then 0x94a0f71934320420580000259829c64d0c8108160000094a0a71934320420580000252831684b8c8108160000095a0a5a12e3204205800002528319c4b4c8108160000095a0a6712d3204205800002528317f4b4c8108160000095a0a5fd2d320420580000252831724b4c8108160000095a0a5c92d3204205800002528316c4b4c8108160000095a0a5b12d320420580000252841684b4c8108160000095a0f5a12d320420580000252839684b4c810816 else 0x94a0a71934340420580000259829c64b4d0108160000094a0a5a12e328420580000252831684b4ca108160000095a0a5a12d32842058000025282dc6670c8108160000094e0a7199c320420580000252829c6664c8108160000094a0a7193a320420580000252831684dcc8108160000095a0a5a137320420580000252829c64d8c81081600000a22528293432042058000025291a0a4d0c8108160000094a0a74134320420580000252829cc4d0c810816) else (if i < 3504 then 0x95a0a5a12d320480580000252829c64b4c811c160000094a0a7192d354460580000252829c64b4d0118160000094a0a71937320460580000252829c64d0c81181600000a22528292d32046058000025291a0a4b4c8118160000094a0a7412d320460580000252829cc4b4c8118160000094a0f7192d320460580000259829c64b4c8118160000094a0a7192d320460580000252829c64d0d5108160000094a0c5a12d354420580000256829684b4d510816 else 0x95a0a5a12d320420640000252829c64b4c8118180000094a0a71934320420600000252831684b4c8108180000094a0a5a12d3204805c0000252829684b4d6108170000094a0a5a1383204205c00002528299c4b4c8108170000094a0a5fd2d3204205c0000252829734b4c8108170000094a105a12d3204205c0000256829684b4c8108170000094a468697f4b4c80580000252829c64b4c8124160000094a0a71934320480580000252831684b4c812016))))) else (if i < 3776 then (if i < 3648 then (if i < 3584 then (if i < 3552 then (if i < 3536 then 0xa22528299c27042074000025291a0a6709c1081d0000094a0a7519c27042074000025284dc66709c1081d0000094e0a7199c270420740000288829684b4c81201c0000094a0b7199c270420700000252829c64b4c81241b0000094a0a7192d3604206c0000252829c64e8c81081b00000a22528292d3204206c000025291a0a4b4c81081b0000094a0a7492d3204206c000025283dc64b4c81081b000009660a7192d3204206c0000252829684b4c812019 else 0x94a0b719684b44207c0000288829684b4d51081f00000a220a5a13c3204207c0000252829c64d0c81081f00000a220a6712d3204207c00002888297f4b4c81081f00000a220a5dd2d3204207c0000288851684b4c81081f0000094a0c5a12d3204207c000029b829684b4c81081f0000095a0a5a12d3204207c0000252829c66709c12c1d0000094a0a7199c2c4420740000252829c6670ac1081d0000094a0a719a4270420740000252829c66849c1081d) else (if i < 3568 then 0x95a0a4b4c827046108000020a719684b4c8130210000089e0a719684b442084000020a719684b4d71082100000829c65a13d32042084000020a7199c4b4c81082100000829c65fd2d32042084000020a719784b4c8108210000091a0a5a12d32042084000020a759684b4c81082100000855c65a12d320420840000253829c65a12d1082000000a220a5a12d3204c07c0000252829c64b4c81181f00000a2227829684b44207c000029489dc65a12d1081f else 0x9620a5fd2d3209c10800002568297f4b4c8270420000094a0c4d12d3209c1080000256829344b4c8270420000094a0a6712d3207c10800002528297f4b4c81f04200000a2252829343207b108000025282934320b11e84200000a220a5a12d3204c1080000252829c64b4c8124420000094a0a71934320481080000252831684b4c8120420000095a0a5a12d3204810800002529192d3209c11c420000094a0a7192d3544610800002528312d3209c11842)) else (if i < 3616 then (if i < 3600 then 0x94a0c6752e3209c10800002568299d4b8c8270420000094a0c5fd2e3209c10800002568297f4b8c8270420000094a0c6912d3209c1080000256829a44b4c8270420000094a0c6752d3209c10800002568299d4b4c8270420000094a0e6712d3209c10800002568319c4b4c8270420000094a0c6712d3209c10800002588299c4b4c8270420000095a0a6712d3209c10800002528397f4b4c8270420000095a0c5fd2d3209c10800002528317f4b4c827042 else 0xa2252829363209c108000025291a0a4d8c8270420000094a27719363209c108000025291a274d0c8270420000094a46869343209c108000000094a0c4d0c82704200000a2262829343209c108000028c9660a4d0c8270420000000256829343209c108000029b94a0a4d0c82704200000a3252829343209c108000028894a0a4d0c8270420000095a52829343209c108000025991a0a4d0c8270420000094a46829343209c10800002528320a4d0c827042) else (if i < 3632 then 0x94a0c6712d3289c10800002568299c4b4ca270420000094a0c5fd2d3289c10800002568297f4b4ca270420000094a0b719a43209c1080000253829c6690c827042000009a2528319c3209c10800002528d60c670c82704200000a225282d9c3209c108000025291e0b670c827042000009a6568299c3209c108000028994e0a670c8270420000094e468299c3209c10800002568d20a670c82704200000a2252829993209c108000025291a0a664c827042 else 0xa32598292d320a6108000025991a0a4b4c8298420000094a0c6712d320a010800002568299c4b4c8280420000094a0c5fd2d320a010800002568297f4b4c8280420000094a0b7199c3b09c1080000253829c6670ec270420000094a0b7199c3749c1080000253829c6670dd2704200000a2252829343409c108000025291a0a4d0d02704200000a32598292d3409c108000025991a0a4b4d0270420000094a0a6752e3289c10800002528297f4b8ca27042))) else (if i < 3712 then (if i < 3680 then (if i < 3664 then 0x94a0c5a12e320b11080000256829684b8c82c4420000094a0c6712d320b110800002568299c4b4c82c4420000094a0c5fd2d320b110800002568297f4b4c82c4420000094a0c5b12d320b110800002568296c4b4c82c4420000094a0e5a12d320b11080000256831684b4c82c4420000094a0c5a12d320b11080000258829684b4c82c4420000095a0a5a12d320b110800002528292d438c82c44200000a225282934320a6108000025291a0a4d0c829842 else 0x94a0a71934320b41080000259829c64b4c82d0420000094a0a71934340b11080000259829c64b4d02c4420000094a0a5a12e328b11080000252831684b4ca2c4420000095a0a5a12d328b1108000025282dc6670c82c4420000094e0a7199c320b11080000252829c6664c82c4420000094a0a71936320b1108000028894a0a4d0c82c4420000094a4682934320b11080000252829cc4d0c82c442000009660a71934320b11080000252829c64d0c82c442) else (if i < 3696 then 0x95a0a5a12e3b0c810800002528319c4b4ec320420000095a0a6712d3b0c810800002528317f4b4ec320420000095a0a5fd2d3b0c810800002528316c4b4ec320420000095a0a5b12d3b0c81080000252839684b4ec320420000095a0c5a12d3b0c81080000252831684b4ec32042000009620a5a12d3b0c81080000256829684b4ec320420000094a0a4b50e3b0c81080000252829c64d0d5320420000094a0c5a12d354c81080000256829684b4d532042 else 0x94a0c5a12d3d0c81080000256829684b4f4320420000094a0a719343c4c81080000259829c64b4f1320420000094a0c5a12d3b8c81080000256829684b4ee320420000094a0b7199c3b0c81080000253829c6670ec320420000094a0a719993b0c81080000252829c64d8ec3204200000a2252829343b0c8108000025291a0a4d0ec320420000094a0a731343b0c81080000259829c64d0ec320420000094a0a719343b0c81080000252831684b8ec32042)) else (if i < 3744 then (if i < 3728 then 0x94a468292d434d510800002528297f4b50c354420000094a0a719343c4d01080000259829c64b4f1340420000094a0a5a12e3b8ca1080000252831684b4ee328420000095a0a5a12d3b8ca108000025283dc668137320420000094a0f7197f4dcc8108000028894a0f5a137320420000094a4983d684dcc8108000025283dc66812d320420000094a0f719824b4c8108000028894a0f5c92d320420000094a4983d724b4c81080000252829c64d0f432042 else 0xa2252829724b4d5108000025291a0a5c92d354420000094a46869684b4d5108000028894a0f5a12d354420000094a4983d684b4d5108000000094a0c5a12d3544200000a2268829684b4d5108000028898a0a5a12d354420000000256829684b4d5108000029b94a0a5a12d3544200000a2252829684b4d5108000025694a0a5a12d354420000094a49829684b4d5108000025291a0a5a12d354420000094a0c829684b4d51080000252829c64d12d35442) else (if i < 3760 then 0xa2252829684dcd5108000025291a0a5a137354420000000252829c64d0d51080000252829c66912d354420000094a0a719a04b4d5108000028894a0a6712d354420000094a468299c4b4d51080000252829d06712d354420000094a0f7199c4b4d51080000252829c66712d354420000094a0a719824b4d5108000028894a0a5fd2d354420000094a468297f4b4d51080000252829d05fd2d354420000094a0f7197f4b4d51080000252829c65fd2d35442 else 0xa2653829684b4ec108000025391a0a5a12d3b0420000095a27829684b4ec1080000252829c66712d3ac420000094a0a7197f4b4eb108000028894a0a5a12d3ac420000094a46829684b4eb1080000252829c66712d35c420000094a0a7197f4b4d7108000028894a0a5a12d35c420000094a46829684b4d71080000268829c65a12d35c42000009a252829c6670d510800002528d20a7199c354420000094a0a719a04dcd51080000252829c65fd3735442)))) else (if i < 3904 then (if i < 3840 then (if i < 3808 then (if i < 3792 then 0x94a0b829c6670ec108000025282dc6671683b0420000094e0a7199c5a0ec108000025282dc65a1423b0420000094e0a71968508ec108000028094a0a719343b0420000094a27829c64d0ec108000025282dc66712d3b0420000094e0a7199c4b4ec108000025282dc65fd2d3b0420000094e0a7197f4b4ec108000028094a0c5a12d3b0420000094a28831684b4ec108000028894a0b5a12d3b0420000094a4782d684b4ec108000028195a0a5a12d3b042 else 0xa6e528292d3209c118000028c94a0a4b4c82704600000a22528292d3209c118000025694a0a4b4c82704600000966468292d3209c118000025291a0a4b4c8270460000094a0c8292d3209c118000028894a0a4b4c81ec460000094a0a4b4c82d07a11800002528292d320b11e8460000094a0a7192d32049118000025282dc65a12d3d0420000094e0a719684b4f4108000000094a0b7199c3b0420000000253829c6670ec108000025394a0a7199c3b042) else (if i < 3824 then 0x9660a7192d320b41180000252829c64b4c82d04600000a22528292d320b1118000025291a0a4b4c82c44600000a22528292d320a6118000025291a0a4b4c82984600000a22528292d3409c118000025291a0a4b4d02704600000a2252829343209c118000025291a0a4d0c8270460000094a4689d2d3209c118000025291a1a4b4c82704600000002528312d3209c118000028898e0a4b4c82704600000a32598292d3209c118000000095a0a4b4c827046 else 0x94a0a7192d3c4d01180000252829c64b4f5320460000094a0a7192d3d0c81180000252829c64b4f1320460000094a0a719343b0c8118000028894a0a4b4ec320460000094a468292d3b0c81180000252829cc4b4ec32046000009660a7192d3b0c81180000252829c64b4ec320460000094a0a7192d354c81180000252829c64b4d02d0460000094a0a71934320b4118000028894a0a4b4c82d0460000094a468292d320b41180000252829cc4b4c82d046)) else (if i < 3872 then (if i < 3856 then 0x94a0a719344b4c8120000025291a0a4b50d320480000094a0a6092d430c812000002528297f4b50c320480000094a0a7192d320491200000252829c64b4ec320470000094a0a7192d320b511c000026894a0a718c82704700000002529192d3209c11c000028894a0a4b4c8270470000094a468292d3209c11c0000294949c64b4c8270470000094a467192d3209c11c000028094a0a7192d3b0460000094a27829c64b4ec118000000094a0a7192d35446 else 0x94a468297f4b4c8120000028894a0a5c92d320480000094a46829724b4c8120000025291a1b5a12d3204800000a225283d684b4c812000002529260f5a12d320480000000252831684b4c812000002889a20a5a12d3204800000a2262829684b4c8120000000095a0a5a12d3204800000a6e52829684b4c8120000028894a0a5a12d320480000095a52829684b4c812000002529260a5a12d320480000094a46829684b4c812000002528320a5a12d32048) else (if i < 3888 then 0x94a46829684dcc8120000000094a0a71934320480000094a0a719a54b4c81200000252829c66912d320480000094a0a719a04b4c8120000028894a0a6712d320480000094a468299c4b4c81200000252829d06712d320480000094a0f7199c4b4c81200000252829c66712d3204800000a2252829824b4c8120000025291a0a6092d320480000094a0a741824b4c8120000025283dc66092d320480000094a0a719824b4c8120000028894a0a5fd2d32048 else 0x94a0a719844b4c81300000000a220a5a12d3204c00000a2252829684b4c8130000025291a0a5a12d3204c00000a520a719684b4c81300000288829c65a12d3204c0000000252829c64b4c81240000252829c66712d354480000094a0a719824b4d5120000028894a0a5a12d354480000094a46829684b4d5120000026894a0a7199c320480000094a34829c6670c81200000252829c668137320480000094a0a719824dcc8120000028894a0a5a13732048))) else (if i < 3968 then (if i < 3936 then (if i < 3920 then 0x94a46869a44b4c8270000029b94a1a5fd2d3209c00000002528397f4b4c8270000025286a0c5fd2d3209c0000095a1a8297f4b4c8270000025283a0a5fd2d3209c0000094a0e5fd684b4c82700000252839685092d3209c0000094a0c5fd2d374c827000002568297f4b4dd3209c000009620a5a12d374c827000002528317f4b4c82c49c0000095a0a5fd2d320b12700000258829684b4c82c49c0000094a27829c65a12d1300000252829c66712d3204c else 0x98e52829c64b4c82d0000026294a0a71934320b100000a22628299c4b4c82c4000000094a0c5fd2d320b100000002568297f4b4c82c4000025694a0a5fd2d320b10000094a0c8297f4b4c82c4000026294a0c5a12d320b100000a6e62829684b4c82c400000009620a5a12d320b10000098a56829684b4c82c4000025894a0a5a12d320b10000094a0c5fd684b4c82c400002568297f5a12d320b10000094a0c5a1424b4c82c40000256829685092d320b1) else (if i < 3952 then 0x2528312d32048034000000095a0a4b4c81200d00000002528312d35442034000000095a0a4b4d51080d00000002528292d32049014000000094a0a4d0c81200500000002528292d35446014000000094a0b670ec1080500000002538299c3b042014000000094a0a4d0d5108050000000288829684b44c008000000094a463209c11c020000094a1a829c65fd2d354000025286e0a719824b4c800000a2262829684b4f4320000025291a1a5fd2d3b0c8 else 0x2568297f4b4c8064000000094a0c5fd2d3201800000002528397f4b4c8058000000094a464b4c811c1600000002528312d32046058000000095a0a4b4c81181600000002528313432042058000000095a0a4d0c81081600000002528392d3209c05400000009492d3209c11c1400000002528312d320b104c000000095a0a4b4c82c411000000025282dc63b04203c000000094e0a718ec1080e00000002588292d320b10340000000a220a4b4c81300d)) else (if i < 4000 then (if i < 3984 then 0x28994e0a670ec108000000094e468299c3b042000000028894a0a4d0d5108000000094a46829343544200000002528319c4b4d5108000000095a0a6712d3544200000002528317f4b4d5108000000095a0a5fd2d354420000000252831343b0c8108000000095a0a4d0ec32042000000025283134320b1108000000095a0a4d0c82c442000000020a5a12d3204c088000000094e0a7199c10820000000025282dc66704207c00000009620a5a12d3201a else 0x2529192d320b511c00000009a252918c82704700000002949a1c63209c11c0000000a6e524b4c827047000000028894a0a4b4d5118000000094a468292d3544600000002528312d3b0c8118000000095a0a4b4ec3204600000002528312d320b4118000000095a0a4b4c82d046000000025282dc6670f4108000000094e0a7199c3d042000000025282dc6690ec108000000094e0a719a43b042000000028894a0b670ec108000000094a4782d9c3b042) else (if i < 4016 then 0x2588299c4b4c82c4000000094a0e6912d3209c000000028889e0a5a12d1300000000a5227719684b44c00000002888299c4b4c81300000000a220a6112d3204c000000029b829684b4c81300000000a22528292d32049000000025291a0a4b4c81240000000a22528293432048000000025291a0a4d0c8120000000094a0c6712d3204800000002568299c4b4c8120000000094a0c6092d320480000000256829824b4c8120000000094a464b4ec32047 else 0x2528317f4b4f4320000000095a0a5fd2d3d0c80000000258829684b4f4320000000094a0e5fd2d3b0c80000000252831a44b4c82c4000000095a0a6912d320b1)))))))) (i % 16)
def starts (i : Nat) : Nat := field 13 (if i < 2016 then (if i < 1008 then (if i < 480 then (if i < 240 then (if i < 96 then (if i < 48 then 0x38b9be0db66bc34e9a00cc664631497f0bba5be2c895c0aa253228593a899a4ae248919087a41c1f78f3875e3921ba8d6067231a17c8b6857629a13788943de1a50b7851823a0d304e81c8082000 else 0x5652b29594aca558aac5562ab1558aac5530a9854c2a61530a9854c2a61530a9854c2a61530a9854c2a61530a9854c2a614a6a0f4e526192848fe46aa2a110a8684232074fec7c93d61e24ec073e) else (if i < 144 then 0x58aac5562ab1558aac5562ab1558aac5562ab1558aac5562ab1558aac5562ab1558aac5562ab1557cabe55f2add56eab755baadd5652b29594aca5652b29594aca5652b29594aca5652b29594aca else (if i < 192 then 0x5ec2f1578abb05d82e6d736b855c2adb16d8b595acacdd62ab1558aac5562ab1558aac5562ab1558aac5562ab1558aac5562ab1558aac5562ab1558aac5562ab1558aac5562ab1558aac5562ab15 else 0x627b13d89ec4f627b13d866c33619b0cd866c1d60eb07583ac1d60eb07583ac1d60eb07583ac1d60eb07583ac07603b01d80ec07603b01d80ec07603b01d80ec07603b01d80ec07603afc57e2bd8))) else (if i < 336 then (if i < 288 then 0x627b13d89ec4f627b13d89ec4f627b13d89ec4f627b13d89ec4f627b13d89ec4f627b13d89ec4f627b13d89ec4f627b13d89ec4f627b13d89ec4f627b13d89ec4f627b13d89ec4f627b13d89ec4f else 0x6b535a9ad4d6a6b535a9ad4d6a6b535a9ad4d6a6b535a9ad4d6a6b535a9ad4d6a6b53559aacd5669f34f9a7cd1c68e3419a0ccf1678b3719b8cc7663b29594ac9063cb19989ec4f627b13d89ec4f) else (if i < 384 then 0x6e036a5b28d816b535a9ad4d6a6b535a9ad4d6a6b535a9ad4d6a6b535a9ad4d6a6b535a9ad4d6a6b535a9ad4d6a6b535a9ad4d6a6b535a9ad4d6a6b535a9ad4d6a6b535a9ad4d6a6b535a9ad4d6a else (if i < 432 then 0x74c3a61d30e9874c3a61d30e9874c3a61d30e9874c3a61d30e9874c3a61d30e807403a01d00e80736b9b5cdae6d736b9b5cdae6d736b9b5cdae6d736b9b5cdae5972cb965c6ee3770ab801bd4dd5 else 0x7583ac1d60eb07583ac1d60eb07583ac1d60eb07583ac1d60eb07583ac1d60eb07583ac1d60eb07523a91d48ea47523a91d48ea47523a91d48ea47523a91d30e9874c3a61d30e9874c3a61d30e98)))) else (if i < 720 then (if i < 576 then (if i < 528 then 0x77f3bf9dfcefe77f3bf9dfcefe77f3bf9dfcefe779bbcdde6ef3779bbcdde6ef3779bbcdde6ef3779bbcdde6ef3779bbcdde6ee87743ba1dd0ee87743ba1dd0ee87743ba1dd0ee87743ba1d98ecc else 0x79a3cd1e4ef2778ebc75e3af1d78ebc75e3af1d78ebc75e3af1d78ebc75e3af1d78ebc75e24f127893c49e24f127893c49e24f127893c49e24f127893c49e24f127893c49e24f087843bf9dfcefe) else (if i < 624 then 0x7b1bd8dec6f637b1bd8dec6f567ab3d59eacf567ab3d59eacf567ab3d59eacf567ab3d59eacf567ab3d59eacf567ab3d2de96f4b7a5bd2de96f4b7a5bd2de96f4b7a5bd2de96f4b7a5bcf9e7cf34 else (if i < 672 then 0x7b1bd8dec6f637b1bd8dec6f637b1bd8dec6f637b1bd8dec6f637b1bd8dec6f637b1bd8dec6f637b1bd8dec6f637b1bd8dec6f637b1bd8dec6f637b1bd8dec6f637b1bd8dec6f637b1bd8dec6f63 else 0x7bcbde5ef2f797bcbde5ef2f797bcbde5ef2f797b73db9edcf6e7b73db9edcf6e7b73db9edcf6e7b73db9edcf6e7b1bd8dec6f637b1bd8dec6f637b1bd8dec6f637b1bd8dec6f637b1bd8dec6f63))) else (if i < 864 then (if i < 768 then 0x7dfbe9df4efa77d3be9df4efa77d3be9df4efa77d3be9df4efa77d3be9df4efa77d3be9df4efa77d3be9df4efa77d3be9df4efa77d3be9df4efa77d3be9df4efa77cd3e41f20f907c83e0df06f79 else (if i < 816 then 0x7e63f31f98fcc7e63f31f98fcc7e63efdf7efbf7dfbefdf7efbf7dfbefdf7efbf7dfbefdf7efbf7dfbefdf7efbf7dfbefdf7efbf7dfbefdf7efbf7dfbefdf7efbf7dfbefdf7efbf7dfbefdf7efbf else 0x7ebbf5dfaefd77e63f31f98fcc7e63f31f98fcc7e63f31f98fcc7e63f31f98fcc7e63f31f98fcc7e63f31f98fcc7e63f31f98fcc7e63f31f98fcc7e63f31f98fcc7e63f31f98fcc7e63f31f98fcc)) else (if i < 912 then 0x7f13f89fc4fe27f13f89fc4fe27f13f89fc4fe27f13f89fc4fe27f13f89fc4fe27f13f89fc4fe27f13f89fc4fe27f13f89fc4fe27f13f89fc4fd77ebbf5dfaefd77ebbf5dfaefd77ebbf5dfaefd7 else (if i < 960 then 0x7f13f89fc4fe27f13f89fc4fe27f13f89fc4fe27f13f89fc4fe27f13f89fc4fe27f13f89fc4fe27f13f89fc4fe27f13f89fc4fe27f13f89fc4fe27f13f89fc4fe27f13f89fc4fe27f13f89fc4fe2 else 0x7f13f89fc4fe27f13f89fc4fe27f13f89fc4fe27f13f89fc4fe27f13f89fc4fe27f13f89fc4fe27f13f89fc4fe27f13f89fc4fe27f13f89fc4fe27f13f89fc4fe27f13f89fc4fe27f13f89fc4fe2))))) else (if i < 1488 then (if i < 1248 then (if i < 1104 then (if i < 1056 then 0x85ec2f617b0bd85a42d21690ab855c2ae14509884742160f907383441a20d106883441a20bf05382540da04b025812c09604b02580cc041ff8ff37f13f89fc4fe27f13f89fc4fe27f13f89fc4fe2 else 0x886443221910c886443221910c886443221910c87943ca1e50f287943ca1e50f287943ca1e50f287943ca1d30e9874c3a61d30e9874c3a61d30e9874c3a619f0cf867c33e19f0cf867c31a18d0c6) else (if i < 1152 then 0x903481a40d206903481a40d206903481a40d206903481a40d206903481a40d206903481a40d206903481a40d206903481a40d1fd8fa47ae3c51d88e6c7123771b18d3467631b15d8a6c47621910c else (if i < 1200 then 0x976cbb65db2e296bca9e52728a940c9da4c925492148ea47523a91d48ea47523a91d48ea47523a91d48ea47523a91d48ea47523a91d48ea47523a91d48ea47523a918c8c6463231918c8c6451217 else 0x9e3cf1e78f3c79e3cf1e78f3c79e3cf1e78f3c79e3cf1e78f3c79df4ed67593a19cb4e3670937a9b84d9e6cf3679b3cd9e6bd35e9af4d7a69533f99b4cb6645317982cbda5ed2f6976cbb65db2ed))) else (if i < 1344 then (if i < 1296 then 0xa1ed0f687b43da1ed0f687b43da1ed0d2869434a1a507283941ca09d02a7f53e99ec4f1e78f3c79e3cf1e78f3c79e3cf1e78f3c79e3cf1e78f3c79e3cf1e78f3c79e3cf1e78f3c79e3cf1e78f3c7 else 0xacad62aab5546a8b540a9ef4eea6fd33693b49da4ed22e8ef467a2ad11687b43da1ed0f687b43da1ed0f687b43da1ed0f687b43da1ed0f687b43da1ed0f687b43da1ed0f687b43da1ed0f687b43d) else (if i < 1392 then 0xad9d6ceb675b3ad9d6ceb675b3ad9d6ceb675b3ad9d6ceb675b3ad9d6ceb675b3ad9d6ceb675b3ad9d6ceb675b3ad9d6ceb675b3ad9d6ceb675b3ad9d6ceb675b3ad9d6ceb49595acad656b2b595 else (if i < 1440 then 0xae9d74eba75d3ae9d74eba75d3ae9d74eba75c6ae3571ab8d5c6ae3571ab8d5c6ae3571ab8d5c6ae3571ab8d5c6ae3571ab8d5c6ae3571ab8d5c6ae3571ab8d5c6ae3571ab8d5c6ae3571ab8d5c6 else 0xae9d74eba75d3ae9d74eba75d3ae9d74eba75d3ae9d74eba75d3ae9d74eba75d3ae9d74eba75d3ae9d74eba75d3ae9d74eba75d3ae9d74eba75d3ae9d74eba75d3ae9d74eba75d3ae9d74eba75d3)))) else (if i < 1728 then (if i < 1584 then (if i < 1536 then 0xaf0d786bc35e1af0d786bc35e1af0d74eba75d3ae9d74eba75d3ae9d74eba75d3ae9d74eba75d3ae9d74eba75d3ae9d74eba75d3ae9d74eba75d3ae9d74eba75d3ae9d74eba75d3ae9d74eba75d3 else 0xaf0d786bc35e1af0d786bc35e1af0d786bc35e1af0d786bc35e1af0d786bc35e1af0d786bc35e1af0d786bc35e1af0d786bc35e1af0d786bc35e1af0d786bc35e1af0d786bc35e1af0d786bc35e1) else (if i < 1632 then 0xb0dd86ec3761bb0dd86ec3761bb0dd86ec3761bb0dd86ec3761bb0dd86ec3761bb0dd86ec3761bb0dd86ec3760bb05d82ec1760bb05d82ec1760bafed7f6bfb5efaf7d7bebdf5efaf7d7bebc35e1 else (if i < 1680 then 0xb1fd8fec7f63fb1fd8fec7f63fb1fd8fec7f63fb1fd8fec7f63fb1fd8fec7f63fb1fd8d6c6b635b1458a2c51628b1458a2c51628b1458a2c51628b1458a2c51628b1458a2c51628b1458a2c51628 else 0xb26d936c7f63fb1fd8fec7f63fb1fd8fec7f63fb1fd8fec7f63fb1fd8fec7f63fb1fd8fec7f63fb1fd8fec7f63fb1fd8fec7f63fb1fd8fec7f63fb1fd8fec7f63fb1fd8fec7f63fb1fd8fec7f63f))) else (if i < 1872 then (if i < 1776 then 0xb2dd96ecb765bb2dd96ecb765bb2dd96ecb765bb2dd96ecb765bb2dd96ecb765bb2dd96ecb765bb2dd96ecb765bb2dd96ecb765bb2dd96ecb765bb2dd96ecb765bb2dd96ecb765bb2dd96ec9b64d else (if i < 1824 then 0xb4559eacf567ab3d59decef677b3bd9decef677b3bd9a6cd3669b34d9a6cd3669b34d9a6cd3669b34d9a6cd3669b34d9a6cd365bb2dd96ecb765bb2dd96ecb765bb2dd96ecb765bb2dd96ecb765b else 0xb505a82d416a0b505a82d416a0b505a82d416a0b505a82d416a0b505a82d416a0b505a82d416a0b49da4ed27693b49da4ed27693b49da4ed27693b49da4ed27693b49da2ad1568ab455a2ad1568a)) else (if i < 1920 then 0xb5e5af2d796bcb5e5af2d796bcb5e5af2d796bcb5e5af2d796bcb575abad5d6a0b505a82d416a0b505a82d416a0b505a82d416a0b505a82d416a0b505a82d416a0b505a82d416a0b505a82d416a0 else (if i < 1968 then 0xb655b2ad956cab655b2ad956cab655b2ad956cab655b2ad956cab655b2ad956cab655b2ad956cab655b2ad956bcb5e5af2d796bcb5e5af2d796bcb5e5af2d796bcb5e5af2d796bcb5e5af2d796bc else 0xb765bb2dd96ecb765bb2dd96ecb765bb2dd96ecb765b86dc36e1b70db86dc36e1b70db86dc36e1b70db86dc36e1b6c5b62db16d8b6c5b62db16d8b6c5b62db16d8b6c5b62d956cab655b2ad956ca)))))) else (if i < 3024 then (if i < 2496 then (if i < 2256 then (if i < 2112 then (if i < 2064 then 0xb8cdc66e33719b8cdc66e33719b8cdc66e33719b8cdc66e33719b8cdc66e3370cb865c32e1970cb865c32e1970cb7e5bf2df96fcb7e5be6df36f9b7cdbe6df36f9b7cdbb2dd96ecb765bb2dd96ec else 0xb8cdc66e33719b8cdc66e33719b8cdc66e33719b8cdc66e33719b8cdc66e33719b8cdc66e33719b8cdc66e33719b8cdc66e33719b8cdc66e33719b8cdc66e33719b8cdc66e33719b8cdc66e33719) else (if i < 2160 then 0xb8cdc66e33719b8cdc66e33719b8cdc66e33719b8cdc66e33719b8cdc66e33719b8cdc66e33719b8cdc66e33719b8cdc66e33719b8cdc66e33719b8cdc66e33719b8cdc66e33719b8cdc66e33719 else (if i < 2208 then 0xb8e5c72e3971cb8e5c72e3971cb8e5c72e3971cb8e5c72e3971cb8e5c72e3971cb8e5c72e3971cb8e5c72e3971cb8cdc66e33719b8cdc66e33719b8cdc66e33719b8cdc66e33719b8cdc66e33719 else 0xb8e5c72e3971cb8e5c72e3971cb8e5c72e3971cb8e5c72e3971cb8e5c72e3971cb8e5c72e3971cb8e5c72e3971cb8e5c72e3971cb8e5c72e3971cb8e5c72e3971cb8e5c72e3971cb8e5c72e3971c))) else (if i < 2352 then (if i < 2304 then 0xb8fdc7ee3f71fb8fdc7ee3f71fb8fdc7ee3f71fb8fdc7ee3f71fb8fdc7ee3f71fb8fdc7ee3f71fb8fdc7ee3f71fb8fdc7ee3f71fb8fdc7ee3f71fb8fdc7ee3f71fb8fdc7ee3f71fb8fdc72e3971c else 0xb8fdc7ee3f71fb8fdc7ee3f71fb8fdc7ee3f71fb8fdc7ee3f71fb8fdc7ee3f71fb8fdc7ee3f71fb8fdc7ee3f71fb8fdc7ee3f71fb8fdc7ee3f71fb8fdc7ee3f71fb8fdc7ee3f71fb8fdc7ee3f71f) else (if i < 2400 then 0xb9adcd6e6b735b9adcd6e6b72fb97dcbee5f72fb97dcbee5f72fb97dcbee5f72fb97dcbee4b725b92dc96e4b725b92dc96e4b725b92dc96e4b725b8fdc7ee3f71fb8fdc7ee3f71fb8fdc7ee3f71f else (if i < 2448 then 0xba8dd46ea3751ba8dd46ea3751ba8dd46ea3751ba8dd46ea3751ba8dd46ea3751ba8dd46ea3751ba8dd46ea374bba2dd16e8b745ba2dd16e8b745ba2dd16e8b745ba2dd16e7773bb9ddcd6e6b735 else 0xbb4dda6ed3769bb4dda6ed3769bb4dda6ed3769bb4dda6ed3769bb4dda6ed3769bb4dda6ed3769bb4dda6ebb75dba8dd46ea3751ba8dd46ea3751ba8dd46ea3751ba8dd46ea3751ba8dd46ea3751)))) else (if i < 2736 then (if i < 2592 then (if i < 2544 then 0xbc4de26f13789bc4de26f13789bc4de26f0777dbbeddf6efb77dbbeddf6efb77dbbeddf6efb77dbbeddf6efb773bb9dda6ed3769bb4dda6ed3769bb4dda6ed3769bb4dda6ed3769bb4dda6ed3769 else 0xbdb5edaf6d7b6bd75e96f37795bc7de3ef1f78fbc7de3ef1f78fbc7de3ef13789bc4de26f13789bc4de26f13789bc4de26f13789bc4de26f13789bc4de26f13789bc4de26f13789bc4de26f13789) else (if i < 2640 then 0xbf35f9afc17e0bf05f6afa97d4bea5f52fa97d4bea5f52fa97d4bea5f52fa97d4bea5f52fa97d4bea5f22f917c8bde5ef2f797bcbdb5edaf6d7b6bdb5edaf6d7b6bdb5edaf6d7b6bdb5edaf6d7b6 else (if i < 2688 then 0xbff5ffaffd7f8bf95fcafe57f2bf95fcafe57f2bf95fcafe57f2bf95fcafe57f2bf95fcafe57f2bf95fcafe57f2bf95fcafe57f2bf95fb2fcd7e6bf35f9afcd7e6bf35f9afcd7e6bf35f9afcd7e6 else 0xc05602b01580ac05602b01580ac05602b01580ac05602b01580ac05602b01580ac05602b01580ac05602b01580ac05602b01580ac025ffaffd7febff5ffaffd7febff5ffaffd7febff5ffaffd7fe))) else (if i < 2880 then (if i < 2784 then 0xc11608b045822c11608b045822c11608b045822c11608b045822c11608b045822c11608b02d816c05602b01580ac05602b01580ac05602b01580ac05602b01580ac05602b01580ac05602b01580a else (if i < 2832 then 0xc15e0af05782bc15e0af05782bc15e0af05782bc15e0af05782bc15e0af05782bc15e0af05782bc15e0af05782bc15e0af05782bc15e0af05782bc15e0af05782bc15e0af05782bc15e0af045822 else 0xc1fe0ff07f83fc1fe0d706b82bc15e0af05782bc15e0af05782bc15e0af05782bc15e0af05782bc15e0af05782bc15e0af05782bc15e0af05782bc15e0af05782bc15e0af05782bc15e0af05782b)) else (if i < 2928 then 0xc2ae1570ab84fc27e13f093849c24e127093849c24e127093849c24e127093849c24e127093849c24e127093849c24e0ff07f83fc1fe0ff07f83fc1fe0ff07f83fc1fe0ff07f83fc1fe0ff07f83f else (if i < 2976 then 0xc2de16f0b785bc2de16f0b785bc2ae1570ab855c2ae1570ab855c2ae1570ab855c2ae1570ab855c2ae1570ab855c2ae1570ab855c2ae1570ab855c2ae1570ab855c2ae1570ab855c2ae1570ab855 else 0xc5fe2ff17f8bfc5fe2ff17f8bfc5fe2ff17f8bfc5fe2ff17f8bfc5fe2ff17f8bfc5fe2ff17f8bfc5fe2ff17f8bfc5fe2ff17f8b3c59e29f14f8a7c53e29f1438a1c4ce24f113880c3d61c30cf861))))) else (if i < 3504 then (if i < 3264 then (if i < 3120 then (if i < 3072 then 0xc62e31718b8c5c62e31717f8bfc5fe2ff17f8bfc5fe2ff17f8bfc5fe2ff17f8bfc5fe2ff17f8bfc5fe2ff17f8bfc5fe2ff17f8bfc5fe2ff17f8bfc5fe2ff17f8bfc5fe2ff17f8bfc5fe2ff17f8bf else 0xc8e647323991cc8e647323991cc8e647323991cc8e647323991cc8e647323991cc8e647323991cc8e647323991cc8e647323991cc88641b20d8fdc7ee3db1e18eac72636f1a38cbc62e31718b8c5) else (if i < 3168 then 0xcbce5e72f396dcb6e5b72db96dcb6e5b72db967cb0e55f29d947ca0e4df25d928c91648b245922c91648b245922c8e647323991cc8e647323991cc8e647323991cc8e647323991cc8e647323991c else (if i < 3216 then 0xcc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cbfe5ff2ff97fcbfe5ff2ff979cbce5e72f3979cbce5e72f3979 else 0xcc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985))) else (if i < 3360 then (if i < 3312 then 0xcc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985 else 0xcc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985) else (if i < 3408 then 0xcc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985 else (if i < 3456 then 0xcc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985 else 0xcc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985)))) else (if i < 3744 then (if i < 3600 then (if i < 3552 then 0xcc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985 else 0xcc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985cc2e61730b985) else (if i < 3648 then 0xcc5e62f31798bcc5e62f31798bcc5e62f31798bcc5e62f31798bcc5e62f31798bcc5e62f31798bcc5e62f31798bcc5e62f31798bcc5e62f31798bcc5e623311988cc2e61730b985cc2e61730b985 else (if i < 3696 then 0xcc5e62f31798bcc5e62f31798bcc5e62f31798bcc5e62f31798bcc5e62f31798bcc5e62f31798bcc5e62f31798bcc5e62f31798bcc5e62f31798bcc5e62f31798bcc5e62f31798bcc5e62f31798b else 0xcc8e647323991cc8e63b31d98ecc5e62f31798bcc5e62f31798bcc5e62f31798bcc5e62f31798bcc5e62f31798bcc5e62f31798bcc5e62f31798bcc5e62f31798bcc5e62f31798bcc5e62f31798b))) else (if i < 3888 then (if i < 3792 then 0xcca6653329994cca6653329994cca6653329994cca6653329994cca6653329994cca6653329994cca6653329994cca6653329994cca6653323991cc8e647323991cc8e647323991cc8e647323991 else (if i < 3840 then 0xcd466a33519a8cd466a33519a8cd466a33519a8cd466a33519a8cd466a33519a8cd466a33519a8cd466a33519a8cd2e69734b9a2cd1668b3459a2cd1668b3459a2cd1668b3459a2cd1666f329994 else 0xcdee6eb3759bacdd66eb3759bacdd66eb3759bacdd66eb3759bacdd66eb3759bacdd66eb36f9b7cdbe6d33699b4cda66d33699b4cda66d33699b4cda66d33699b4cd6e6b735b9abcd5e6af3579a8)) else (if i < 3936 then 0xcece7673b39d5ce8e7473a39d1ce8e73739b9cdce6e73739b9cdce6e7373939c9ce4e7273939c9ce4e7273939c9ce4e7273939c9ce4e70b3859c2ce0670337b9bdcdee6f737b9bdcdee6f737b9bd else (if i < 3984 then 0xcece7673b39d9cece7673b39d9cece7673b39d9cece7673b39d9cece7673b39d9cece7673b39d9cece7673b39d9cece7673b39d9cece7673b39d9cece7673b39d9cece7673b39d9cece7673b39d9 else 0x67673b39d9cece7673b39d9cece7673b39d9cece7673b39d9cece7673b39d9cece7673b39d9cece7673b39d9cece7673b39d9cece7673b39d9cece7673b39d9))))))) (i % 48)
def edges (i : Nat) : Nat := field 25 (if i < 3312 then (if i < 1656 then (if i < 816 then (if i < 408 then (if i < 192 then (if i < 96 then (if i < 48 then (if i < 24 then 0x912a00240500204a6008013010571003494801302401aa47001803805e91800500c014a45001092800601403e6c8011a44003402003e90c00c00600ca42003c010080d84017482007001 else 0xc93b00040d802c4ea00e03500fdca004c9d001b06801ca67002c13806299801804c015a65005412804a990011048010a63000411807095c00a14e00481700c12b002c05802a4aa00a015) else (if i < 72 then 0x161b104e2b4804512429c3f10171b083b8b4404512201daa700b833807ac9c03a52e01405700f1930068a580270ac01ba870088238066a180081ac00384600b542803a1140364ee00f037 else 0x12db407a2b60045130202bf70131b3874eb5c04512e207bf60135b306f2b5804512c22b3f50141b28662b5404512b0023f48011b24008b52000129001bf3800db1c006b4e0001262633f2)) else (if i < 144 then (if i < 120 then 0x9c969008a2485397e2036361077568808a24404f670027337012073808c35c05586a0293a501518a809432004917002dc13015dc180b4bcc04726c028b75014dba00acdcc0596e41fdbf8 else 0xf496c008a2620077ef003b67801d6bc00025c4107ec030b660de96b008a2584577ea0323650cc96a808a2560047e900236480116a40002504b87e60343630a4569808a24c4c77e4034b62) else (if i < 168 then 0x2edb18524b4c0451262643f202f5b104e6b48045125000bf18005b0c002b46000122031b3801899b80bc39c0676300333a50118aa00be2e006b5e602e9360195ba80d4dc83fc7f0030368 else 0x2fdb907fafe009a6d01e9ad801144c080cfdc09b6ce1d42d701144bc00cfda0066cd0032d68000db400049a00012c22c3f502cdb28666b5404512a2533f402e5b205f4b5004512825cbf3))) else (if i < 288 then (if i < 240 then (if i < 216 then 0x108014002d86001483000091800000815ece00991f005433702607b80e639c0a076c046176027dd301165980b774a04f3960208ab00ec2e009d70c0409460305798138dda00026c05ab75 else 0x301b9010a94807b0242293f702c5b38886b5c0a948e0210071151fb0164d984295ac0512460108030168d9409348a02100502e9b2011c91004200805e363021d21808400c0be6c4042242) else (if i < 264 then 0x11c1a015a99c07716e03a82702913301060980954ca03f82502413200fa0900c25e6044a63020011815495c07102e051a5601c00b016cdd40944aa03d015023d2a00f20500884a603e013 else 0x8005b0c002b460001220582a70284338158a5c0920ae053a9601d07300e41580ab50e04684702994300ba1180b874a04ba85022822815c9dc07806e052a7602181b012c9d407e06a048a74)) else (if i < 336 then (if i < 312 then 0x801db3c00eb5e00012e208bf60319b306f6b5804512c22cbf50325b28668b5404512a253bf40331b205f6b5004512825d3f30335b18526b4c045126264bf20339b104e8b48045125000bf1 else 0xa5169808a24c4ca7e407036209d569008a24a0017e3000b61800568c0002440c8670063b37030c738196e940c41700682f301c09b0194dd40cf6e41ff3f80315b407a8b60045131003bf7) else (if i < 360 then 0x371ba81c2dca0087f100436880216c40002604077ee06bb670ea56b808a25c4127ec06c3660df16b008a25845a7ea06db650cd56a808a2544a87e806f3640bf16a008a2504bb7e606fb63 else (if i < 384 then 0x80004a8952fd01296c817ead401144a0978fcc12b6c614aad30114498996fc812d6c413b2d20114490a74fc41336c20ef2d101144881b4ce00d966e06a8e70375d281ac2e00e25e6038936 else 0x42dc281e45141315e60391360429ba81d84d412f6e41ffbf80419b407aab60045131003bf7801db3c00eb5e00012e209bf6041db306fab5804512d002bf58015b2c00ab5600036b000125))))) else (if i < 600 then (if i < 504 then (if i < 456 then (if i < 432 then 0x4b1b181f490c04300609736203dd21008600853b7e209a361077d6881de904043002084b3804219b8240ca01051d008db27800073822ac980ff1cc086ba503f4b28218e540f12aa0740b8 else 0x1d09a80e60541024a807581403ed2981dc04c1306e407c25203b409024ad9c11d48e0218078019b3400c91a00012d0000060499b2822091404300a2553f404a9b205fcb50101488021804) else (if i < 480 then 0x3a81b82329d80f906c089a7503d41a82089d0048068090a6703a45b81ce09c1184cc07b02604493281e80941034c807802404c97981f898c0f304608f25703540b822e9580c302c088a55 else 0x8009b14004b4a0003650001228000490a78fc41846c20f02d10114488248a9c1160ce094327048d4b821e15c12764c08e29604382b023ea1c10008e08d2860178230228a140fe08a091277)) else (if i < 552 then (if i < 528 then 0x8021b44010b620001302043f70521b38754b5c04512e20a3f60525b306fcb5804512c22dbf50531b2866cb5404512a255bf4053db205feb5004512825ebf30541b1852cb4c0451270013f2 else 0x7856882809040440020a5b3805299b81ce39c14e74a0bbaf880005c02debdc14716e0b42f605145b02c2bd414316a0ae2f405045a02aabcc14416603a9360535ba82a2dc813e2650043f8) else (if i < 576 then 0x4fc09400ed9e00748f00009780000382f6d9816d48c02200605f1b282cc91404400a0bfb64057d2200880101826c60ad2430110018a6afc81836c42812d2054d21008800853d7e20c2b61 else 0x5581a02f099c13b04e0b826605481302d299414604a0b126405081202ba98c0490460ba25703580b82dc9580c402c0b3a5501dc9a80ec0541806e80b025404f40a02b694c13c0260aa252))) else (if i < 696 then (if i < 648 then (if i < 624 then 0x1144882f4a9c16c0ce0bf32705e54b82ca15c17d64c0b9a9605902b02eca1c15e08e0b928603a46b01d011816b50a0ac04505d53b82b20dc1714ec02f83605a93a82ae0d41817280b1a74 else 0x1144b882afd818a6cc1bfad601144b08b8fd418d6ca19bad501144a8958fd01906c81802d401144a4006fce0036c7001ad38000498998fc81926c413bad20114490a7cfc41956c20f12d1) else (if i < 672 then 0x9e169033a24a0017e3000b61800568c00024418c6700c5b3703a873831ee9419160e0250c404ec5c0328bcc07826c0c7375064db94010fe20086d10042d880004c0812fdc1896ce1d5ad7 else 0x689d282782e01a55e603c9360685ba8348dc83d65b00228980eb16b808a25c3805ac0228961175fa8340d943385aa0ce8958011fa4008d920045a90000940a5d69808a24c4cd7e40d1b62)) else (if i < 744 then (if i < 720 then 0x1144c075ab5c04512e1c1ad601144b400afd60056cb002ad580004a8602b5019d12814c2d306ac49899cfc81b16c413cad206b0494002fc60016c3000ad1800048833ece019e66e0758e7 else 0xce96a83582543025a80ce8940a6569835624e0027e5001362800969400024a0017e3000b61800568c0002441ae6700d6b3703b0738360e9413d1700d9af301e89b035edd41b26e41ebad8) else (if i < 768 then 0x741b104f4b481ab125000bf18005b0c002b460001220deb3806f19b81da39c1c074a09f0b807097980f64d81bf6ea0e0b720f616c008a2603ae5ae0228970e116b008a25845f7ea0df365 else (if i < 792 then 0x3b873839ee9413f1700e92f301f09b039cdd41d16e41ecad801144c075eb5c04512e1c32d601144b08c0fd41cd6ca19dad506ac4a8606b50045129001bf3800db1c006b4e000126267bf2 else 0x114538704b981e314c22f405079dba8672b941e414b0024048011ba4008b9200114814f2e3011451c00500a0026e50012e280045100fa4981e86ca0f536207d5b0833a4841cc6700e5b37)))))) else (if i < 1224 then (if i < 1008 then (if i < 912 then (if i < 864 then (if i < 840 then 0xc2972008a292003807001b73800d71c00228c4fe8040feb7209fd7103ee28807e24c0fd36507f1b10410d841ab2420f333807959b81e039c1e974a0a08b807ad7987b6ba00451501d82e7 else 0x8009b94004b8a00114403f9260831b2841cd8821c6c20d612107e59c03f0cdc0f11ce0fdba505085c03fcbcc3de5d00228a80ec573808a29c3875cc0fb0a6801602c00add60055cb0008a5) else (if i < 888 then 0x895b1045ed841ab242105b3808299b81e439c20d74a0a18b8083d7987beba00451501d9ae7011453870ab9820914d002c058015bac00ab9600114a184ae4079052053eb8c1f7147001402 else 0x3cc738448e941441701132f30f8d74008a2a03b25ce10f8a70e2173044029833f5ca0fb8a50c3172008a292003807001b73800d71c00228e002805001372800971400228808024c111b65)) else (if i < 960 then (if i < 936 then 0x114540768b9c21f14f0034068019bb400cb9a00114c1a02e5082452861ab901e31481502e3088051c00500a0026e50012e280045101024982356ca11bb620919b0808a484222670110b37 else 0xd057283ec29430e5c80228a4800e01c006dce0035c70008a313fe01049adc82805c41100a20208930494d9424c6c412b3610114908468ce023366e07a0e708d9d2828a2e02385e61f22e8) else (if i < 984 then 0x87c51c00500a0026e50012e2800451010649825e6ca130b6209adb0808a48424967012433703d4738496e941461701272f30f9574008a2a03b65ce10f8a7801a03400cdda0065cd0008a6 else 0x7049084bace025c66e07b0e7097dd2828e2e02625e61f32e8011454400f01e0076ef003ae7800453883101825b6ec1c4ae6087c530684b9404514a187ae4011452098300c2606e6151ae3))) else (if i < 1104 then (if i < 1056 then (if i < 1032 then 0x13b17384c229c4e55cc11b8a6137972841c2944d95c80f50a4134971844a28e002805001372800971400270a0012650008a214fd6c010a49827d6cb0013628000d9400048a000125001361 else 0xa11b28518d8804524426836109f19c04f6cdc0f81ce13f3a50f9d7c030c2e03b55ee1320b70e297b047675823928c11d0b60d197a842c2d43155e80f90b40aa179845a2cc4f55d00a88a8) else (if i < 1080 then 0x1145c400f05e00770f003af780085b883705828170c1c5af6087c5b068ebd404516a18b2f401145a400704e003707001af380085982a42a05015c62834020a89b90a00b8821f264043126 else 0x800dc1c00474e0022870010b30550540a6500c2a86e62822e308b0998a06b885415b00441260a71b28a80b520036c70001b3800091c00024c4d16c2141b380a099b81f239c28574a1f52f8)) else (if i < 1152 then (if i < 1128 then 0xaa1b183b448c4d26c20e11210a6d9c0534cdc0fb1ce14eba50fad8403323203b760e1440c70e318304a47982502ac1288c60d2d82840a31431c6080d30c413017c097ebdc4be5ec02b0b4 else 0x800dc1c00474e0022870010b314a57402aa2a05205ce1310a714657304702985125ca1078a514357203d6292003807001b73800d71c00270e0012670008a3800d71044c28808924c153365) else (if i < 1176 then 0x790998a10b8808a24c156b650ae1b1833a48c4d46c2152b380a919b81f839c2a774a1f73080668640770c1c2a118e1c6b060964630698c1421d18a18eb0407b0620986be04c25ee02b8b4 else (if i < 1200 then 0x1149189aad842ac670155b3703f473855ce943da6101548c80ee583808a31c38160c1550c6801612c00ae5600560b0018c58012124008e520046090018c40b99c1808a50c156150171b73 else 0xaa4640774c1c04518f0034268019cb400cc1a00318c240c250af1ca867cc142aa18b0024248011ca4008c12003188173b830114a182ae2a02e46e60f193314257101164982bb6ca163b63))))) else (if i < 1440 then (if i < 1320 then (if i < 1272 then (if i < 1248 then 0x801983400631a00584b002b95801582c00631430b6081550c40ba1c183ec50c158150172b730824998a14b8808c24c1663650b6db1808a48c4d66c215d3380ae59b81fc39c2bd74a1ee308 else 0x8011ca4008c1200318818bb830114a182b22a03106e6022933142d71011a4982ec6ca17ab6301149189aed842cb67016533703fc73859ae943e06101548c80eed83808a31e00684d003396) else (if i < 1296 then 0x8000da40004920001282a02d21361b085d6ce02ea66e0800e70bb9d2c0110a2008731004308800c64077cc1c04518e20fc260ba5cb0720c182a918c243c250bb5ca869ec142a918b002424 else 0xb086b094b0d430874a1a93150adc6a895ec204ae60e256b060c1dcac008e520033c9001954800c620638e101d3288029943056c54062add01f42682862e215096b811e4983066cb002364)) else (if i < 1368 then (if i < 1344 then 0xc75c2044e51015c150299ae78011ba40027120012690008a414357101204983136ca18ab6407249209b2d8430567018233704087387bac602f11b01dfb1703446b8722c582c33ec160966 else 0x8c49a0a1cb8809124c18d3650c71b203b04904db6c21893380c459b820639c3e86301790d80f018b84c635c39262c16f8d60d4d8a85903544b061018a3958011ca40067920032a90018c4) else (if i < 1392 then 0xc659c0630cdc1041ce1f63180bcc6c0782c5c2871ae1c9b160b846b06a8c542c91aa258b080c6dcac008e520033c9001954800c620988bde0047090011d48008a240042d015d15018eb74 else (if i < 1416 then 0x108a1b063ce9839662c1548d680161ac00ae9600562b0020d50c89ca896709034e7282593040aa4aa0690e100452880af0a80d0dba008a4d05105c40491260c85b28656d9004524826e361 else 0x58054068cdd421a26a230b7408309a0a22b885435ae04a1268015b2c0006d600024b0000958015b2035e4904dd6c21903380c7d9b820a39e0088710043a880218c40083603c462e0228d7)))) else (if i < 1536 then (if i < 1488 then (if i < 1464 then 0xe5d9305a08182ce2ec1678e611e58c064236047462e0850d711b58b059835a00586b002ba580158ac0087d60042cb0020d50d49ca85685544657281569540d2dc2840c5144637080fd144 else 0x80106a86a6e542b62aa2413940d31c2846051416115029a2e78015bac00271600126b0008a5144971012a4983466ca0e51251185b209bcd8433d67019e3370f859406463a03c564e09c0e7) else (if i < 1512 then 0x8008a2c0042d41621501a637508c89a8a26b8809624c1a5b6507649288c6d904e06c21a2b380d119b87d2ca03281d01e33270998738730c982e01cc241b18042c6bc00ae960043eb002165 else 0x6e89288cad901b0248270b610d299c0692cdc3ed6501948e80f1d93851239c39964c1710e612158c021835e00574b0021f58010b2c00835435472a1579551211ca098abde00570b0011d5)) else (if i < 1584 then (if i < 1560 then 0x8010fac0085960041aa25ab0812d183c00ae560033cb001955800c62c00ae502ae2a81aa38507fca28908e101fb28802a143058c5406a6dd421826a24137408349a0a2ab8809724c1a9365 else 0x87c9a8a2cb8809824c1af36501149288ced904e26c21a8b380d419b87c4ca034d1d01e432704d4738734c982dd1cc24eb180c886c0930c5c10d1ae248b160b346b400b0d600574b002b15) else (if i < 1608 then 0x11a1b209c6d843576701ab3370fbd9406aa3a200788f003bb7801d93c00a39e00688d0033b6801993400a39810e1ae1b43a50114b286cee540452aa245b940d91c2843e5141641501b1375 else (if i < 1632 then 0x8021dc4010ca20051d01e5b270d5473c00d11a00676d003326801473021e35c39574a1549650e3dca855255448c7281bbb850114a282ca2a03766ea022935145d7101324983716ca022925 else 0x8014bb400a3981111ae1cbba60b64b30722e582c42ac246b940e31c304aa5181671501c537609109b0a30b8a0066cd0001b6800093400025809c24a234b641391b086d4ce036966f004448))))))) else (if i < 2472 then (if i < 2064 then (if i < 1848 then (if i < 1752 then (if i < 1704 then (if i < 1680 then 0xe49cb058c55848e7281c6b860960a302d02a20066ed0009c680049b40022985195c41c5366070c93013a49446a6c8272b610fc59c06dc3e03cc66e1ae0f7105d94082cc9e00676d002a06 else 0x80085b02d22a038d6ec1239361469710718d981d424c04f12511adb2097cd884e76c21f9b380dbc7c079acdc3611ee20d328106593c00ceda00540d002976801473022435c39874c16d166) else (if i < 1728 then 0x27c9288d8d904ad6c62743610fd19c06e03e03ce66e1b18f7107994083ac9e00676d002a068014bb400a3981131ae1ccba60b70b30726e582be2ac20e395123dca400ce1a0023ad001146 else 0xd607b8842ca042064f0033b6801503400a5da0051cc08a0d70e69d305b059a00672d0019e6800cab40063184907281c9b86093ca30838e1416a1501c9376090c9b0a38b883916cc0d4126)) else (if i < 1800 then (if i < 1776 then 0x8014bb400a3981151af0033a68010fb400859a0041ac1cd3960b14ab0922e5039970c12b94605ac540730dd824526c28eae20e5db303684980a024a236b6413a5b087e0ce038e1f01e7b37 else 0xf0dd3008a5983bd72c022956124dca074ae1804528c0b60a80e8dbb008a4d851e5c41d0b66011493014249446f6c82753610fc99c07283e03d066e1ae8f71091940846c9e00676d002a06) else (if i < 1824 then 0x8000dbc00049e00012e0519251511fa08e0d905435a82a12d313adb0c01116200879100433880187c400f15e00778f003b3780187b884eca042664e21ac460f29db084ac983552ec08b0d7 else 0x80187b8856ca03cc76e1ada070d64bb86b439c45588c2053b610a993078ae9c1b93ee0db96706e06b822e3583bf72e0d39571251ca076ee1c28b28e0b70a80ed5bb84d44dc51f5c5003b67))) else (if i < 1944 then (if i < 1896 then (if i < 1872 then 0xf01cb83dc55c4957281dc3870a38a382de2a20076ef0009c780049bc00229c5345c8299ae3148171076ad9c1c424e05212511c5b209d8d843f56901ce908102d9c400ef1e00642f003187 else 0x1309b90a42b883b76ce0ea92702949288e4d904bf6c42773610fe1a4073e42040c671003bc780190bc00c61e0061ee216b280f35db86be5dc42c64c1e33a70848fb842059c2111ae08c0d6) else (if i < 1920 then 0xd80bb885cc983c774e1019f70804b3840435c1191ac1e0b9701bcf380da55c06e18e206b961259ca03222e200770f0011d78008a3c0042dc4c55e82622f305c0540770ddc26d26e29b402 else 0x125dca0968c103c170e1431471035c302e22a03c06ee136137148d71077ed9c1a924e05312511cdb2095cd8c4ef6c21fcb480e8084081cce200778f0032178018c3c00c3dc42f6501e73b7)) else (if i < 1992 then (if i < 1968 then 0x6d493814e4944746c82783610fd9a4077842200778f0032178018c3c00c3dc4316501e7bb70d94bb8860c983c874e1599f70ac4b3856435c11a1ad003b97800cf3c00655e00318e25b424 else 0xf0884400ef1e00642f00318780187b8866ca03d076e1b317710c993400ee9e0043ef00216780106b82363583c872e1581571261ca078ee1c28d28e0b90a80f19bb84dc4dc5245c41e2b67) else (if i < 2016 then 0xb28b2879ee5c2bf2ae2103950ae4aa8934e503ce70e1479471075c284905141731501e6b7709bc9b8832dd423326a292ae20f31b381a449c40a6cc20b36502a09288ecd904f16c21fbb48 else (if i < 2040 then 0x13c9b08a7eb443fa6901e4908801de3c00c85e00630f0030f711019406d23a200788f003bb7801d93c00a81e0052ef0028e7801d9306ac3983d074e16b1f70b4cb385aa35c11c1ac211ba5 else 0x1111938876c983e175019516804786b07bae602f42b024db940fadc403ae5203e76f00e39c807189c03902a017414e2932e28021b440006e200025100009802a89288eed905415a42a2bf1))))) else (if i < 2256 then (if i < 2160 then (if i < 2112 then (if i < 2088 then 0x7bc9c03e22a017514e258373149d7107bada01aa25005592511e1b2095ed8c4f36c30043d8801d14400e6620072101fabc80e70c40802f1c3f17701b62080dacbc06da3a045388e2003b7 else 0x100de387e0ee03722f0222b2710f19307c4ea032c2d008f8d68021cc40067a20032b10018c8019c63096f09049c72825ab040fb1c4032e7601962900cc0b81009c38962e0c3e86f00f81c8) else (if i < 2136 then 0xf89cc05ec56049d7281f6b880810a4090ae103e96f010a1c8084c9c042a2a017614e241b7414a17107c2da01b625005612511e5b209e8d860087b1003a28801ccc400e4203f67901cd988 else 0x80045402ee29c5295c41f3b68071494015a49447b6c827ab618021ec400e8a20073310039080fdde4073c62040478e1f93b80dccbc088cc9c43d64d0043a88010fc40085a20041b00900d6)) else (if i < 2208 then (if i < 2184 then 0x11f1b20980d884f76c30043d8801d14400e6620072101fc3c80e88c407e6ee03742f0223b2710f99307d2ea032e2d00908d60fa1cc05ee56049f7281f738808aca44010de2001391000938 else 0x112193887ec983ed75019696804886b07d8e602ef2b02013971281ca4010e220023b100114880085c07dcde022939011413808a85402f029c537804261b7214a97107d6da01d6250057125) else (if i < 2232 then 0x924a287e6de024039011f13809045402f229c41a6ea11a13514b17107e2da00e3250200367105db2815e49447d6c827c3618021ec400e8a20073310039080fe5e407486203f47701ba978 else 0xe98c44011122008771004328801504400a5e20051d10043270da8738880c983571cc1f93a80cbcb4024635842474a1659650fc1cc05f056042172a15d1551285ca07e8e2025329020f385))) else (if i < 2352 then (if i < 2304 then (if i < 2280 then 0x100dcb8944e503f97101451481039c307f0de026839013393809a45402f429c40c6ec296ae20fd5b401cc4a04016ce205b6602c09288fcd904f96c30043d8801d14400e6620072101fd3c8 else 0x9ed2083780060087b1003a28801ccc400e4220087910032188018c4400c3e04518901fd3b811419406f05e044e64e220b260fddd4064c7e03252d01938d81011d382483583f6730178158) else (if i < 2328 then 0x9700a868895020a028188a530794098a5cb882a44a411081210ed2381b201c43648c06a126034c0308aad9442a48a06380511fdb206789101ad00818224306780185349081cb00427d361 else 0xba81b88729d82c006c21827501881a8946e503504e815583410fd33831609c4384cc14802610b93285040943494c80fc0240c6131809c08c43e4ae0be8a705280b886e95827002c216255)) else (if i < 2400 then (if i < 2376 then 0x67c0185369081cc00427db6109f120837a00445166e2212a710d0338882a5c4260af0033b680194b400a39a0050ac21ea870c7c238874a182d71ac16a04610c942824e35410808a21e277 else 0x111d2b02fc29814b02c216a5509740a868a95020b0281892530798098a5eb882a54a411101211292381c849c0e500e229b6611112301b401842b48a0640051201b2067a9101ae008182a43) else (if i < 2424 then 0x4a06a82121144494ee17c83711153b05d60d84314ea0318351291ca06a29d02ac068226a67095013889099818c04c217a650a0c1286949901f904818ca63013c11889895c24214e11f817 else (if i < 2448 then 0x801122400025200000818324306840185389081ce00427e36109f520837e00600778f003aa780187bc00c19c45176e227a9710a02b889ca584270ac225a870cc023888ca1832008c219a85 else 0x1441188f695c18014e0a681711c52b04bc05846a4aa11a81511892a04360503134a60f401314c171054c94822302423ba470370038a88b5847048c06500611a522816c4940b500b002364)))))) else (if i < 2880 then (if i < 2664 then (if i < 2568 then (if i < 2520 then (if i < 2496 then 0x11d543027435813908c2372850b48b285a21144784ee17603711cd3b00ca0d846c4ea15d8351295ca08cc9d02b506823e26706381388e499828404c235a6509281288c899020704818d263 else 0x32c03091a9140b824a05b8051295b209109101bb008183a43068801853a9081cf00427eb6109f920838000447e54e23786712019388faa5c4680ae23fb2611d94b08ce15847a50e192047) else (if i < 2544 then 0x123d32849609448a4c81000240c6d3180aa50c05204624fa57060453829c05c4954ac12f81612392a846c0544894a810c8140c512983d204c5315c4153a52089009093691c0dd00e24a246 else 0x122c2b093ca1c48608e24ca8604dc6b026c11849250a16f04512dd8389389dc2ee06e25b306125d3b00cc0d84904ea15e8358011ca40089d2003189001834128133831e09c4964cc142826)) else (if i < 2616 then (if i < 2592 then 0x3840389d69180cf00c272245030092817e0144fc6c826ea4406c80209b090c1a4006268a420744014002d860014830000918000008944a9c4930ce25232712854b891815c4a364c24d296 else 0x13401309ce99424c04a27026407f01209b698c05904627b257062053830e05c4ed4ac13281613992a847a4d423c02a26fa54085c0a09b494c1f30262992e2134d29045c0485455ae279247) else (if i < 2640 then 0x13e14b89c615c4fa64c278a9613882b09e8a1c4dc08e27828604c06b025e1184e950a26b04513cd3b89ae0dc4ef4ec03503613a13a89aa0d44fd728270a7413501a09ee99c19304e277266 else 0x8009b9400494a00114500081214992381c401c51f48c06800614612281844940c100a298364144522036601050c4860d280314c9b10a0e9081db004281a4107480089f2a9c4ea0ce27db27))) else (if i < 2760 then (if i < 2712 then (if i < 2688 then 0x14ad3383382dc19b04e2912661414130a3699425a04a28a2640878120a1e98c1ed04629bae714a92b832805c5365cc290a5614040b0a3495424e02a289a5407f80a0a1c94c05b14602d013 else 0x14b5538a3c19c52f64e296297145c2b8a5cc9852552c28b05614a1438a2011c52450c0990d604c4230a3aa1450a08a293a77142c1b8a469d806b06c28e27514241a8a62e505154e8284034) else (if i < 2736 then 0x156d930aa035855218e2a88b715be098abee0c5635e62a69351575ba0abcdcc5626e4519bf71561b39462b5ca367ec2acb6628c16b0ab4d960046c9000094800db1c00024c5606c42b8b61 else 0x153c6b0a9831856f8482b639415b9820aa62dc54e26a2b5b7415b5b98ae0dc8bae7ee2b2b672eb16b9760fd85666cc5d5ad6159db28ad4d920036c70000938009b140002485726c22ae327)) else (if i < 2808 then (if i < 2784 then 0x1c99f88b4ed8467c5a22c4b271621930b0435858418e2c18b71652098b1ce0c5915e62c0935162dba0b1adcc5906e42c2b671619b30b0ed9458a6c82c6363163db10b2ad8456964e2b4326 else 0x1691820b46e0c59b6ef0033768004530bed01459e6ea2e3ae51681ba0b44dcc6388042d2b7216f1710d7afdc59a6ce35d2d71b05fb0b38d986b65ac2ceb65167db20b42d8e0026c5000092) else (if i < 2832 then 0x16b1bb0b5cdd45b26e8318c0316d1b98c48b8c63b8042dab7216f5710ed8fdc5aa6ce3b4ad71dbdfb0b56d987665ac2d6b6516c5b20b66d8e0026c50000921f0df88b6cd847385a22cc0c7 else (if i < 2856 then 0x1761b291eeb5454612a4f23f417b1b211b4b50546128524bf317f9b19158b4c54612653dbf21831b11142b48546125000bf18005b0c002b460001222cc0e616c1d28b5ee160076ef0008a7 else 0x151c4994f8fc860d6c44512d2151c494002fc60016c3000ad18000488b343985e774a2d50b71899798bc6dd461b6e5003bf7801db3c00eb5e00012e4b13f61745b31224b5854612c4b9bf5))))) else (if i < 3096 then (if i < 2976 then (if i < 2928 then (if i < 2904 then 0x17a1d28b562dc6275e62f23751871b912c4fdc5d16ce4acad7151c4bc00cfda0066cd0032d680004b12e8fd45d96ca47c2d5151c4a93cafd05ed6c846dad4151c4a1494fcc5ff6c6456ad3 else 0x1805b18c1ed8a0016c30000911664730bd2e945ad16e3142f31789ba8c3adc89737ee2ec36725c56b92e8fd85d96cc4b7ad68015b2c0002545ee6c83003631839b14002d860001222ce0e6) else (if i < 2952 then 0x1841b14002d860001222d40e617a9d28b5e2dc6295e62cb8a718fd73400add600114a31f2e31912010c3cdc863d5c44d1bf7178db39340b5c9a57ec2f236626756b400ad9600012a2f7b64 else 0x180db1915cb4c6116c5000b618000488b4c3985fb62e2fd3168015d2c00835454d2a82d80b718a9798bd4dd461f6e44e93f7179db393a0b5c9d47ec2f436627396b0bd2d945f06c8301363)) else (if i < 3024 then (if i < 3000 then 0x2935fa0c06d90a435a9001b638000498c24d8a0016c30000911674730be2e945b116e315af317bdba8c40dc89e47ee2f636727896b93cafd85ed6cc4f02d617b9b2c008d92000128526bf3 else 0x29e56b94f8fd860d6cc53bad61839b28c22d906126c70013628000494002d860001222cf8e61809d28b662dc62f5e6300b751885b91492fdc5fe6ce523ad72929fb0bfed98a455ac300365) else (if i < 3048 then 0x1901724004dca001144563bf7186db39588b5cac97ec30e3662b056b0c3ad946206c8310b638009b1400024a0016c30000911684730c20e945a916e3162f3183dba8c34dc8a7b7ee306367 else (if i < 3072 then 0x8008598c52dd462d6e659c3f71899b3966cb5cb3a7ec313b662cd16b0c50d9462b6c831636318b9b14002d860001222d18e6187dd28b6e2dc62d5e63212e71658530c8901461e6ea320ae5 else 0x1955ba8cbab8c65f80432d3721971711292fdc6526ce495ad72561fb0ca6d989115ac32a365195db20cb0d8c6596c5000b618000488b4839862a74a2dc8c718cd7b8c64bd854e169001b83)))) else (if i < 3192 then (if i < 3144 then (if i < 3120 then 0x19d1798c8a29867780a33737519d9728ceab906736e449dbf719adb39254b5c9657ec336366244d6b0cdad946706c8338b6319c9b14002d860001223270e61959d28c9e2dc65b5e63268a7 else 0x1a15ba0e0100c6876e637a2e31c4a010d12dc868f5c433f3678019b340002586806ca3ca3f41a11b20e96b506866c63dabf21a21b10e7ab487d27e2345b611ce5688cce39866f74a3340b7) else (if i < 3168 then 0x801db3c00025e0066cd0000961abdb2942efd06c86c846ead42975f98da8d8c8af5a65473f21b85b11146b48c037e2383361208d688d06c9c68264c2cc145801dbbc00229c67f6ec340b75 else 0x1ae1930d002dc6f75e62cc9351bb1b90d5ed9e0066cd0000968015b2c000254a187e8364b6423796a0daad8c6e26c46023f11c1db09048b446bf64e35cb2619f85b8decbcc59b26a375b72)) else (if i < 3240 then (if i < 3216 then 0x1af19bc00ceda0051cc2bb9651b0dca8d042dc6f85e63271361b09ba8ddadc86b96cf00336680004b400ad9600012a50cbf41b29b211beb506d66c6371b623015f88e10d848255a235db27 else 0x1c29b0904eb44548123003bc780187b8d78edc69616e3418b61be5798cce4dc6c06ec3773721aedb38d7cd9a0056cb0000952869fa0d96d908e05a836bb631b91b1180cfc47096c24132d1) else (if i < 3264 then 0x1b21b3941cb5c54812f0033f68019b3400cb5a00012c50c3f51b25b293feb5454812b0023f48011b24008b5200012852f3f31b61b19160b4c548126547bf21b95b11148b48548124603bf1 else (if i < 3288 then 0x16809a8de0dc8a5d7ee36a367296d6bc00cd9a00012c36ab652979fa0db0d90a565a9001b638000498dccd88c087e2385b6120a1688d96c9c6ca64c3420b71be9798b3c4d46ef6e450bbf7 else 0x1b8d930cfa2dc6fb5e62d11351bc5b9151cfdc6e16ce5462d78019b340002586e26ca547bf41b95b2150eb506e66c70013628000491812fc470c6c2414ad11b5d938dacc9868616e37f2f3)))))))) else (if i < 4968 then (if i < 4128 then (if i < 3720 then (if i < 3504 then (if i < 3408 then (if i < 3360 then (if i < 3336 then 0x1c3db09058b446ee64e376b261a285b8d285146fc5e638a2e7168c9ac004dca001144375b678019b340002586ec6ca570bf41bbdb2154eb506f06c6378b623029f88e1ad8482a5a2372327 else 0x8005f8c002d860015a30000911be5938df0c9868d18e3812f71c057b0a9e2d20037070010b316909a8df8dcc6f66cf00336680004b0deed94b527e837d3642c696a0df6d8c6fd6c46073f1) else (if i < 3384 then 0x300dfb8e0cd9cbfa5ae2a50978019fb400cd9a0065ad0000963011fa8e0ed94beb5aa2a5095301dfa0e14d90bdd5a82a50943021f98e16d8cbd55a62a50933025f90e18d88bd15a42a5092 else 0x1540aa0e2a2dc7245e632313616989a8e46dc87186cf00336680004b0e36d94a0d7e838fb6423716a0e42d8c7226c4607bf11c95b0905ab4470964e3843261a205b8e1ebcc5a526a387372)) else (if i < 3456 then (if i < 3432 then 0x15e0b30e56e5872716e399af316a09a8e64dc872a6cf00336680004b0e58d94a1b7e8397b6423856a0e60d8c7316c45fcbf11cd1b09044b4471a66e38eb271c7a230e32ed871c64c390317 else 0x1dc5930cfe35878a7282d61351e0dba400ed9e00012f00336680004b0ec0d94b697e83bd3642d956a16d8fcc7966c65b1ad32e7df90f50d88afe5a4625bf11eddb0905eb4472e64e396b26) else (if i < 3480 then 0x2c0169189afc47b96c2418ad11da9938ed0c986811ac3c5b9416a49a8f08dd20076cf0000971d81b3400ad9600012a3bdb641e5db19740fc87a96c457fad23131f88f70d848305a23b9327 else 0x1e65b19744fc87ab6c4580ad23139f88f74d848325a23b5b378019db400a39874a1ac3410d51e31ca0c9e4d87736ea3c2b74801db3c00025c7686cc3b83651df1b20f30d8cba17e43d5362))) else (if i < 3600 then (if i < 3552 then (if i < 3528 then 0x80004a0f34d8cba37e43d63622c0969189efc47bb6c2419ad1801de3c00c3dc76b76e3418d51db9cb0f1ae5073a28c3341371db5bb0f0cdd20076cf0000978019b340002587726ca3beb64 else 0x80004b8f06d987846ca3c3b641e6db19748fc87ad6c4581ad23141f88f78d848345a23beb271df1930cfa35878e7282d71351e1dba400ed9e00012e5b4bf61de9b316ceb5877b6cb002364) else (if i < 3576 then 0x16c09a8f1edd20076cf0000971e29b30f16d9478e6c83ce3632e95f90f5cd88b045a46293f11ef9b0906cb4478664e3c2b261c9c6b0e9059478f7283e12e616bc9ac008dd2001149003b67 else 0x1e6dba400ed9e00012e5b63f61e59b316d4b587976ca3cd364800db1c00024cba67e43d7b622c156918a6fc47bf6c241bad11e35938f18c987151ac3d0b071e81834008e520031882a8943)) else (if i < 3648 then (if i < 3624 then 0x1ea5b2970eb5454912a5d1bf41eb1b216feb505491285d33f31ebdb196f2b4c5491270013f28009b14004b4a00012462a3f11f01b09070b445491223ccb271e61930d0a35879d7282d9135 else 0x152c4998a8fc87c06c460ead2152c494002fc60016c3000ad18000488f56c9c7aa64c3438d61eb9ca0b684d47ad6e9003bf7801db3c00eb5e00012e5cfbf61ea1b3171eb5854912c5d03f5) else (if i < 3672 then 0x1ee5930d123587be7282da9351ef5ba400efde0076cf003ad780004b9896fd87b76cc61dad6152c4b1898fd47b86ca619ad5152c4a989efd07bb6c8615ad4152c4a18a6fcc7bf6c6612ad3 else (if i < 3696 then 0x1f8db18fd0d887ea6c23e5b271f29930d143587c772e3e73941f10a38b6e4d47cd6e9003b6780004b8f90d987c96ca3e63641f3db1974efc87d06c45832d2310df88fa2d8482e5a23dd327 else 0x1fd1b20feed8cb977e43fc3622bf56918b8fc47fa6c241cad11f7d938fbcc9868c1ac2bc8c61f9a120fc4e507e560839d8b716e09a8fc2dd07e46e63f4b721f6db38fb8d987dd6ca3f0364))))) else (if i < 3912 then (if i < 3816 then (if i < 3768 then (if i < 3744 then 0x16e89a901adc869f12c4712d42031b117f2fc480f6c24112d11fb9e38fe711c7ed76e3f93271fc5930d1a3587f67283fcaf6154c598cc04dc5b926a3fab74801db3c00025c7ef6cc3f8365 else 0x3029f91054d88bd25a440a0928005f8c002d860015a3000091205993902ac9868e1ac40d39416ec9a9032dd074f12e40c3642c1d691886fc481b6c24172d12029939012c9873c16e4072f3) else (if i < 3792 then 0x8005f8c002d860015a3000091209993904ac9873d16e4162f31ca4530b784d48e55c8415b722fed6b8cca25cbf35ac3258962fb16a8c706d45bc24a31b8952f796a1004250bd65a6410093 else 0x20c9939062c9868f1ac41b3941f18538b7a4d48356e85842e231116b8ccc25cc3c5ac32609630d16a8c766d45bd24a31d0953141fa1068d90c2c5a8404094309969900624cc1e5a4410892)) else (if i < 3864 then (if i < 3840 then 0x216db110c4d8484d64e4263261cf85b90a2bcc69f14c473ae42139b990a0dc85bf24a427b62214db09080c9c83f64c3480d6210dca0e9e29c8416e84223732c25710b7c4948426c8423361 else 0x2e5e0110d6dc8afd5c42e112521a5b210d8d8485e64e42eb261a446b10c2e5074f14e42fb742c29710b824948606c8431b6121659390b0c9873f16e42e2f31a7c5311ccb9085a6e42e0125) else (if i < 3888 then 0x2b15739584b9a0026e50008a231756b90ead960026c50000921868908d2639887274a3a00b721dd79925cb9c9155cc439b7221c5b290e8d885c9242434327219d930d2435886a7283a78a7 else 0x1a586a9102e520076ef0008a71da8531618b8866924e43eb6621fdb2110cd8487b64e43d3261a546b1100e5074f14e43cb752c2d710b8649487e6c8442b611a507310ece947c516e43c2f3))) else (if i < 4008 then (if i < 3960 then (if i < 3936 then 0x2271ca0e9e29c8976ec44c3752ea601113adc8b135c42e2125226db2113cd846971cc4463a51d045b9120bcc92f5ce48bae62235b9911edc888b6ca447362172490c00ef1e0061ee43e3b7 else 0x2309d29258c1c91960c460b95230dca0e8c29cb155c44603651724919544d848ba64e45cb261a7c63141b0908bb72846e3041d14539628b885c524a45e3632a85b09134c9c89964c34c0d6) else (if i < 3984 then 0x1ca0731194e949a160e4cf3068015cac00631474814e58bae231816b400ad9600012a2f11232a91b08d343988c974a496b07246983118ee5474714e58b2e22321b28b9248caa36c234c8e6 else 0x2a9db0919ccde00676d0028e68019cb40063186b818a474b041d28539632b8865024c467b652351b1954cd848cd64e4663261a7c631196e548e86083a48a72c61710b8c4948d36c6552b61)) else (if i < 4056 then (if i < 4032 then 0x2aa1b091c0c9c8df64c38b8d628418391b231ca0a60c2be0c6280d82917e31600484900239480118240063109f47062ab1431d2c5393e4dcc83c26658d2e2171c9291cad909f06c6400123 else 0x2aa9b09260c9c95888c4813b62445930d3a3589b67283a68a72c71710b924949856c8554b6123cd9391e4c988f074e34f8d623c5d2945f0909b2728513b041d30539636b885c824a47a364) else (if i < 4080 then 0x15f46314670909b97285153041f6c5b8ea029cbae8045353722c7d710b944949886c8512363298db11558d8493b88e4823b724a993923ac9869e1ac4dbb941d3853963ab885c924a4c3364 else (if i < 4104 then 0x22f4aa9376e5090970a4439451d4853920edd486d26a590ae22415b28b9849498a6c855736124e9939240c986a11ac4dd3941d44539640b885cb24a4c4b642ab5b09272c9c91f64c3500d6 else 0x26c1c20ea829c9af6e8591ae21738929318d90ab06c24a43272489930d463589bc7283a98a72c89710b9a49498b6c8557b61251593920839c92164c4808e61a886b121ae948c42ca485b95)))))) else (if i < 4536 then (if i < 4320 then (if i < 4224 then (if i < 4176 then (if i < 4152 then 0x2639b21564d8494d64e4a63261a946b0b0c318a368484df39428ad820fac2dc75514e5d840229adb91648b885cf24a4c6b642895b194c8d88ab16c24a5327248d9311e035c6a41ac4deb94 else 0x2701ca0eae29cb265c42e9125263db21566d8495f64e4818e7255d9312043986a61ac4873a52314b29218e548be2aa4dfb942429c2911051475614e48437521b89a964ab889066ca2e8125) else (if i < 4200 then 0x25a59392d0c986a91ac4e13941d64539650b885d424a4c8b642ad5b092cec9c96664c3540d62705ca0eb029c89714c5b32e42d9171964eb885d324a4c83642ad1b092c8c9c96364c3538d6 else 0x2cad710ca24949946c855c36124cd93923cc986ab1ac4e23941d6c539654b885c924a4c9b642addb09264c9c92464c3550d6270dca0eb429cb295c42e49252649b2144cd8ca656c455b361)) else (if i < 4272 then (if i < 4248 then 0x24d593923cc986ae1ac4658d5271dca0ebc29cb2d5c42e49252659b21574d8493164e492b261ab46b138ce5075d14e5962e219a892932ad90ab96c249a3272479930d583589c57283ae0a7 else 0x1d88539660b885c924a4ccb642af5b09262c9c92764c3588d62725ca0ec229cb2f5c42e49252661b21578d8493164e4933261ac06b1390e5075f14e43c8a52cb9710b924949976c855db61) else (if i < 4296 then 0x2671b21580d8493164e4943261ad06b1398e5076414e5992e21724929336d90abf6c249bb272479930d663589cb7283b18a72cc5710b9249499a6c855f36124d993923cc986b21ac4e5394 else 0x1b04fa8d385946b61aa4a9b9515ecaa939ce5095170a4549451d9853929edd489426a59a2e2194493129cd9464824a4ceb642b05b09262c9c92964c35a8d62735ca0eca29cb335c42e4925))) else (if i < 4416 then (if i < 4368 then (if i < 4344 then 0x2cd9710cd449c93c6cc3309262681b21588d8493166e48f3b61adc6a939ee5076714e59aae2172493133ed90ac36c249c337258193922039e00688d0033b6801993400a3986b61ac4aaba5 else 0x252db312d4d949a26c8563361801e2bc00ef1e00766f0030f724e1db928ced890f2ec49fba623b8b30d7435493d72c46b9562741ca1286e187d328c3b48a72505bb0ed871874226c3b48a6) else (if i < 4392 then 0x191c029346d908f9488402004238d218ffc00c8b148440e0022b1db0914a904810003003bc780187bc00eede0051ce47b0d71af06a93a2e508a014e3b58a62cdd710cf46dc67924e33d897 else 0x22dc1a12889987d304c48c26522a01291fa990847048476263155011928495876c14c3a101624592a91260548fb4a842a01423a929907404cb385c445a252219009127891866b00c48a245)) else (if i < 4464 then (if i < 4440 then 0x274dca10fa29c81714c59cae28019b340002589a46c862fad231bdf89590d84c5e5a24a3a96243c2b1280a188ee08c48e2851af46a8d3611493e4ec46b836246d3a8af40d49d272847fa74 else 0x23ad29907604cb3a5c445aa5221940912b491866200c4a7245194c02934ad908fa4884028042391218ffe00c8b248440e8022b25b0914c90481100249da1724f0c3928a3dc94b76e3600d5) else (if i < 4488 then 0x1b046a8d3811495b4ec46c03625513a8af60d49d472848027422e01a12bc9987d404c4a926522a41291fc990848048476a6315541192ba95876f14c3a181625412a91280548fc4a842a814 else (if i < 4512 then 0x175492934ed90acb6c24b5337256103129c5d89571cc4678d6202c6a93aae5077314e59dae28015b2c000254c687e84d336431896a18c2b4caca6c24b0a9624402b12b8a188ef08c4ab285 else 0x231cb293ace5077614e59f2e2175c92930ed90acd6c24b732725b5930e2e358a2c60e4dc394155ca18eea29cb3d5c42eb12526a1b21598d8496c64e4b5b261a7c6b1370e5077414e59e2e2))))) else (if i < 4752 then (if i < 4632 then (if i < 4584 then (if i < 4560 then 0x1770929352d90ad06c24bc32725dd930d3e3589d87283bc0a72d01710bb64949876c8567b6125d99392eac987291ac4ebb941ddc53967eb885da24a4c3b642b39b092e4c9c97064c34f8d6 else 0x26e1ca0efe29cb435c42ef125261db215a4d8497c64e4bdb261a7c6b13b4e50a6c5ec3bf0a72d09710bba4949aa6c8568b6125e99392f2c9869f1ac4ecb941de45396d0b9885f1485a0ae2) else (if i < 4608 then 0x178492930ed90ad56c24c13272605930d3e3589db7283c08a72d15710bc04949876c856a36126019392fec9869f1ac4dc3941e00539688b885df24a4d5b642b4db092fcc9c97d64c34f8d6 else 0x2b5db09344cde00676d0028e62348fb11a05988d11ac3968d52775ca0f0a29cb475c432a92631a1fa934cd94c665ab00236480004a15acd8498464e4c1b261a7c6b13b8e5078214e5a32e2)) else (if i < 4680 then (if i < 4656 then 0x26b1930d3e3589b87283c40a72d25710bca4949ae6c856c361801de3c00c3dc9a276e47a9671cb86a93bce5087f14e3c30a62d21710cee6dc66e24e33c0972691b318ceb560046c9000094 else 0x1e30539696b8865624c4eab652775b215b4d8600745100321827462413627e071a3ec51942828d61391387209b464e4d9b261a7c6b1370e5078914e5a52e2179892936ad90ad96c24d6b27) else (if i < 4704 then 0x28ed831472c160047290018c41570a1910229c78d14c5a62e219bc9393a6d989de6c856db6127459bc00ceda0051cc46b0d61c78fa8e2c59471c1aa51d30728e182c008e520031882ad943 else (if i < 4728 then 0x2799b215bad849de64e4eeb261cdcfb0e6a5987361ac46a96528f5839478c1a0047290018c41574a18f1e29cb4d5c4634ad617a892c008d9200012856e361801de3c00c3dc9d176e38e8d5 else 0x27bdca0f2429cb505c42f992527b9b215bed849e964e4f43261b146b13d6e5079114e5a7ae217c89293d4d90ade6c24f1b272785930d883588c32aa4f3b94277dc28f2029cb4e5c42f5925)))) else (if i < 4848 then (if i < 4800 then (if i < 4776 then 0x20480093f0c9c9f764c50931727d86b9416c586c71ac502b1523186a93f8e508bb2a84fdb842124a20f2629c9fa6e842b1342d45710be84949f96c84031242b81b093dac9c9ec64c3630d6 else 0x1e50530e88058a084aa44a81528052a10de0509f34a641e0132d4971116c948866024507a46198c03140e91464900a50024417d8920bea0109f148640000322cd21103c008ae16c2453a41) else (if i < 4824 then 0x2b89b0942ca58a060ac50d31628554313fc118a1962a50628527f42294229d88d906c5052751c7c1a94089d08bf06850a2661f541314129948aa04a50126422241213ea98c556046509a56 else 0x17e492945ad8cae46c2510b272881930d9a358a23728536af61f8c598f3c29cb545c42fc1252889b215c6d84a1d64e50e3261b306b143ee5079514e5b5ae621105196a6b885f724a50f364)) else (if i < 4896 then (if i < 4872 then 0x17ec92147ad8cae66c25193378019db400a398a3962e51c3152834f313f8558a0a18c45594628ddc28f4029cb565c42fd12428f1b195cad84a2964e5143261b3863145cc1079f14e5aaae2 else 0x1b3c6b1484c1ca417282c61431e885396dab885fc24a5203642b9db0c00ef1e0061ee5193b728d5db1476c58a3a62a5171571c80628fcc75c7da28e3f38b728d1c3108a29c7a114c5abae2) else (if i < 4920 then 0x2951b215d4d84a4f64e5273261b446b14a2e507a414e5b7ae218109294a0d90ae96c25243272919930da0358a4472a5263942234a28f4629cb6e5c42fe925292db215d0d84a3f64e51f326 else (if i < 4944 then 0x2dd17110d628860724a530b642bb1b09026484a5864e52bb2629718b8da6358a5a7284271441e985396e2b8860624a52cb642badb094a6c9ca5264c3690d62955ca0f4a29cb705c4302925 else 0x2bb9b094cec9ca6664c36d0d629a5ca0f6029cba85c430412529a1b215dad84a6064e52fb261b646b14c4e50b9b5ce3d38a72e4573112c298b895ca4380a52e057210ae290b7b5c641e8a3))))))) else (if i < 5784 then (if i < 5376 then (if i < 5160 then (if i < 5064 then (if i < 5016 then (if i < 4992 then 0x1d3c5390e64d4b595c430592529f5b21556d84a7364e5393261b706b14ecc1ca757283a78a72d61710c14494a746c8577b6129bd9394dcc986db1ac538b941d3c53963cb8860924a538364 else 0x2a29b215e0d84a8464e541b261b7c6b150ce507c614e5adae2185092950ad90aab6c254032729fd930dbc358a827283a78a72d69710c26494a816c8555b6129e99394f0c986dd1ac53f394) else (if i < 5040 then 0x2d75710c2e494a976c8555b612a45939520c986e71ac549b942a517b0ac22cc7ec14e58f2e21858929524d90af16c2544b272a2193151ac5c6e01ac545b941d3c5390b44d0b5c5c430a925 else 0x800048953cc9ca9d64c3750d62a81ca0e9e29cb1e5c430c9252a7db21556d84a9a64e54cb261ba46b1538e5074f14e5af2e21860929536d90aab6c254b3272a55930dd0358a987283a78a7)) else (if i < 5112 then (if i < 5088 then 0x2d81710ce649cc6f7ec56436631b96b15aed920016c30000912b199bc00ceda0051cc5530d61bb46a95b4e507ca14e44f9362d7d7118dab5c65f36c32d12619784b1594d94ad66c9000b61 else 0x1cc86b1548594adc7283e68a721d49a96c2b88c715ae6382d61910da8c3c49464312b00236480004a4002d86000123003bc780187b958cedc6ee1aa56db94220ce391044dc88414e3e58a6) else (if i < 5136 then 0x2bd5ca0e9e29cb1e5c43111252bd1b215ecd84adb64e56d3261c8c6b15ccc1cae560d002394800c620ac450c7ce14e43b1352d897118e4b5c61f24a56e3648005b0c000244ad764e56b326 else 0x21285216f8b8c5641470014028009b94004b8a0011443121252c0db21610d88b726c240f9212be19395eec986f31ac57d3941d3c53963cb8862324a57cb642bedb095e6c9caf264c3790d6))) else (if i < 5256 then (if i < 5208 then (if i < 5184 then 0x1fb8eb975b020bb280c587b272c39930dea358b117283a78b72c79b90c4a494b106c85893622c05939600c986f41ac5823941fb05b9738b9c7d714e5c92e62bf0531714b9488a14a5c12e4 else 0x2ce5b31690d90b606c459bb378019db400a398b191ac37c0d52d2dca0fe22dcbb55ce5d9ae515a051c004dca00114432d9262cedb2968ed90b5f6c5003a2880190c166f120b1b3f05869d8) else (if i < 5232 then 0x2edd730ad628e0026e50008a231cd6b0c524960046c90000942d85b1400ef1e0061ee59bbb71be46a9698e5089216e3f99d61faca30fe42d8bb65cc5da2e515a451c004dca00114433a127 else 0x2d5d8396acc1a0047290018c41fd85b907c50cbba5ce5dcae6212c520ade70c5632662b60a38009b9400228862a24a5a6b642d89b11690c9cb4764c3998d62c5cb2969ae507f516e5dc2e7)) else (if i < 5304 then (if i < 5280 then 0x20040116e690481f0025b03272d7d930df8358b627283fe1d71feca38ffa2dc89128a5de2e72eed730ae028e0026e50008a231d16b8c5a494b616c90013628000491698c9cb4b64c3920d6 else 0x2e95c1970898cb750465ce2561fe00b1726954afc02a5c5a5422280a170694c84a0265bea52159009173091866400c5c824519280297109106312483180042e91b1970090c8070065bd242) else (if i < 5328 then 0x18c892176ed8cbbb6c25cf2962e382b1744c58b9d50c5c30462e858a972ca14b8508a5cd2762df81b172a9d470018a37f8352e353a16ee0d0b994cc5bc0262e51328afc094b8c4c85bb024 else (if i < 5352 then 0x2ea8a3975ee18bba7065cb9c72dd09b973829c6332485dc3632ef1b0975acdcbb264f0033b68014731768c5cbb362a4290c61c04628b2875859228c2c98b62ec5c29772e0c7f914e5d4136 else 0x1c106b178ec1cbc67282b99431ec8539792b8863524a5e2b642f21b0977cc9cbbd64c3818d62f01ca0f6229cbc25c431a1252efdb21782d8600778f0030f72eb5db976cc58bb562a3810c5))))) else (if i < 5568 then (if i < 5472 then (if i < 5424 then (if i < 5400 then 0x2f4d209028004be464e5f1b262ff98b97c435cbf762c3828d62fc58a97b6354be87285ec9542f9dc217965107b414e5f33742f309a181ab8863624a5f2b64203c921816d84bc464e5e1b26 else 0x2ffd2b0f6a2987b302c5fa2552f400a97dc950bce0285f02532f2809981cb88bd84a45e68122ff1230cca018bf348a39a0052fb5220c704906370085efa4320080197ae908820004606361) else (if i < 5448 then 0x306db09036484c0252c5f905630198b1802a18bea08c602b152fe14297d2114bfd4ec5ee0362fd93a8afe0d4bf04e85ed0343001330fb0098bf54ca5ea0252fbd32179e090be14c62ba023 else 0x30b521901000cc27484401802307d209042004c1864e60bb261c406b1834e50c475ce3db0a730f973182c298c365ca60a0a530b9721824290c285c66080a3308171182628863924a60cb64)) else (if i < 5520 then (if i < 5496 then 0x1600129870990c2204862938330c131984208cc484ac3ec81630fd2a9838054c374a860a81430bd29982204cc294a42ba8123111230fa2018c3d48a32600530d5220c7649063a008628b63 else 0x15d8598f8229cc5b5c431e125315db218b4d84c4a52c61d05631398b1892a18c3208c626b153109429862114c464ec61503631053a8e2431471106a61ca74308c1a188a998c2404c620265) else (if i < 5544 then 0x306c93988825cc5d24863a2d1319593c00ceda0051cc633b17318c6b18d10d4c6474a6333152fe4f317ca558bf318c63015431a5c18f8425cc735a262b3273155930e26358c5872862caf6 else 0x3221b91da2fd8c826cc7682d63b49fa9906d94ecf5aa642364800db1c00024e0026c50000923225b0c00ef1e0061ee6363b631a86b98df0d8c6b74c63731631b58a8e28314c727066219b7))) else (if i < 5664 then (if i < 5616 then (if i < 5592 then 0x32adb21960d8ccb36c5000b61800048992ec58c9662a6488c532485b19204d0c996e664db72324db31928d94c956c864c3633269b11938d84c8662c642b1531dc6298f42d8c75268643b73 else 0x800048993a354cc17286603743a5dfb1976d98e945ac74d3f532f1b29d22b54cbe6c86613633311b14002d860001226508b632dd79996cdc8e177ec654366384d6b1c34fd4caa6ca7082d5) else (if i < 5640 then 0x3c59fb19b0d98f135ac78cbf53365b29e20b54cdb6c86703633389b14002d860001226510b633557999a8dc8ee07ec6653663b716b1dc6fd4ccc6ca76cad53335b2199ed8ccd16c5000b61 else 0x33d1b219ecd8ccf76c5000b61800048993e354ce77286518a633a9711eb6fd8ce56cc7ad2d63d71fa99ccd94f595ab00236480004a19d0d8cce96c5000b61800048993c354cdf72866f374)) else (if i < 5712 then (if i < 5688 then 0x3435b19a1cd88d0f6c267d0d53409ca19f6298d065c46803663d35fa9a02d94f4a5ab00236480004a1a06d8cd046c4682b6133b06a99eae50cee14c67c2e23d59fb19e4d98f545ac679b65 else 0x3b8df89a7ed84df05a26888b634b5799a56dc8d196cd002b6580004a9c2efd0d206c86fe2d43495b19a52d88ee07e269f36137bd689a0e354d0c7286840a63441711a12d98d0a6ca685b64) else (if i < 5736 then 0x34d58a993a4d0d316cd002b6580004a9a66d90ead7e669bb633a41699a74d88f007e26a036137c5689a242d8d2e5e66963723471b3400ad9600012a70d3f43485b21bfab50d266c6695362 else (if i < 5760 then 0x3555b21ab2d8cd5a6c4783bf13579b09be4b44d5488e6abc363c11f89a8ec58d4662a64f1343509b3400ad9600012a6a23643cb9f99a90d8cf0f5a66a53623ce5f89a98d84f0b5a269b316 else 0x35bdb29ae2d90d736c66ba36235ddb09ac22d8d685e66b3b723589b31ac6d94d646c86b2b633599b11ad2d84d5464c6ac31631d8aa1a9e2d8d5c5e6676935356db91aa6d9a0056cb000095)))))) else (if i < 6192 then (if i < 5976 then (if i < 5880 then (if i < 5832 then (if i < 5808 then 0x36c1b09be8b44d111aa6c4b94361dba400cd9a00012c6c0b653615b21b2ad8ce977e46d03623981691e2cfc4daf6c26f9ad135c1931ae4c58c782a86b68b635d97999404d4d756e46b7366 else 0x32849a400cd9a00012c6c7b653645b21b2ed8cead7e46d13623989691e5cfc4db16c26faad134486a9b14e50d886e900336680004b1b04d94d866c86cb3633a69f91b42d88e615a478cbf1) else (if i < 5856 then 0x36e1ca1b6edd0db46cc6dab6536d9b21b72d8cdba6c46ddb6136a58b1b50c54ca226900336680004b1b4ad94da76c86d5b633c01f91b5ad88ef55a479cbf136c9b09daab44d9362c6c9315 else 0x37398a9aa0314d7a16c6529343745b99ba6dc8dcb6cc6e63653735b21ba0d8cdd26c46ea36137158b1b88c54ca42686e0b663709b29b86d90dc66c66e3b623ce5f89b90d84df65a26898d5)) else (if i < 5928 then (if i < 5904 then 0x37a1b21bd6d8cdec6c46f73613759db1a28354ddb7286f0af531e45999f84d8dda6e900336680004b1bb0d94dd96c86eeb633779b11e7cfc4de36c26fbad1375a239bc1058f3b7e26e7b16 else 0x3d59f89c88d84f425a268b8d5380dca1af8298e645c46ff364390db09af6298e635c472136134586a9bf6e50dfa6c86f3b2634546b1bd4e50ded5ec63d8b332989a9bd2dd0de56cc6f3365) else (if i < 5952 then 0x3d35fa1c04d90f495a87a42d3391db09a36354e067286bf8a6399d711c02d90e466c268d0d53815ca1afc298e665c47003643915b09a30354e047286be8a63995711a12258dff6c87a2ad2 else 0x3d2d6ac008d920001287a32d23d6df89c94d84f435a26b18d53825ca1b08298e6a5c47003643925b09a2e354e087286c18a639a5711bfcd90e486c268e8d5381dca1b00298e685c4685095))) else (if i < 6072 then (if i < 6024 then (if i < 6000 then 0x8011ca4006310c7c2866c48a639b5711c14d90e4c6c26bc0d5382dca1b10298e6c5c467c8963d316ac008d920001287a3ad23d71f89c96d84f445a26b50d53829ca1b0e298e6b5c4680096 else 0x383dca1b18298e705c4706b64393db09a3c354e0e7286c58a639bd711c18d90e4e6c26a90d538a5831c50c160047290018c431f4a19b14298e6e5c4705b643935b09aa2354e2560c711305) else (if i < 6048 then 0x3648531ce8b88cef24a70db64394db09c2ac58e1162a6c80a639cd71194e490e526c270c31638498a9b1c298e725c46549243945b09c28c58e1162a6c68a639c571194e490e506c268f8d5 else 0x32b4921cacd84e1f62c70f31535c4aa9c3ae14d9414c73b2e232b0921caad8600676d0028e63859d31bf2298d9314a73aae233f4931c32d94e546c270b3268015d2c008354d552a870e384)) else (if i < 6120 then (if i < 6096 then 0x3668531da5008e396e473cae232bc921c56d8ce376c472c36138918b1c46c54d5618a6e58b63664531da3008e386e473c2e232b8921c54d8ce366c472bb6138858b1c40c54d9814c73bae2 else 0x32c4921cb8d84d241aa718b943674531d16b88e306c872db61348c6a9c5ee50d9c14c7452e238b5b21cb4d84d221aa717394366c531d12b88e2c6c872cb61389d8b1c4cc54d6018a6e48b6) else (if i < 6144 then 0x32d0921cbcd84d281aa71eb9435f8531cf6b88e3b6c8722b61349c6a9c78e50db414c73d2e238e9b21c86d84e3562c71a315367c531d1ab88cb224872eb6138cd8b1c64c54d9e14c7462e2 else (if i < 6168 then 0x8005b0c000244d2b1aa72639436fc531cfcb88f555ac6758953d6dfa1c94d90f525a87a82d38005b0c000244e4162c7203153634531cfab88cb524872fb6138fd8b1c7cc54dc114c73e2e2 else 0x31fc51c004dca001144735b6439f9b11ca8c58e5362a6de8a637e09a1d00b88f5e5ac65b1248005b0c000244d2c1aa726b9436f0531cfeb88f585ac6798953d71fa1c96d90f535a87a8ad3))))) else (if i < 6408 then (if i < 6288 then (if i < 6240 then (if i < 6216 then 0x39d18a9bb82d8eca5cc764ae5320451c004dca00114465b9243a01b11a5c354e6e7286eb8b63b11731d86b94c801470013728004511cd8d90e7f6c46968d539b5ca1baa2d8ec05cc75eae5 else 0x3a6d8a9a64314ea770665e9243a85b19d2ac58e9262a6980c53a99c19974490ea06c67433163a158a9a5e314e8870665c9243a1db19d04c58e8162a6e10c53a11c19970490e836c673ab16) else (if i < 6264 then 0x3a59d31a6c310e9970a75538337789a99fc498e986ca7523633a5993400ae960041aa7478c534d4621d52e0ccf024a74eb643a8db19d2ac58e9362a69a0c53aa1c19974490ea26c674e316 else 0x3acd7b1d64bd60037070010b331f8991982490eac6c67523163a8d8a9ad6314e8e2a87563833d8d6a99804920036c70000933a7d8b1d3cc54d3018a755b8332fc921d4ad8e00676d0028e6)) else (if i < 6336 then (if i < 6312 then 0x3b4db09d74c58eb962a69d8c53af1c1998c490ebb6c675b3163ad58a9a72314eb470c75c38337b09b198a490eb76c6757b163ab98a9a70314eb17066619243ac1b19d54c58ea962a6ae8c5 else 0x3bb9b09d84c58ec162a69e8c532505a9da504cec87067672f3377c531990490ec66c67663623b51b09d7ec58ebe62a69e0c532385a9da304cec7706766af3379053198e490ec56c6765b62) else (if i < 6360 then 0x323caa1dcae10da814c77cae235e4929dc8d90ef16c276f3163b698a9b4c298ef85c46b49243bc1b09dc2c58edb62a6d20a63bdd711996490eef6c276eb163b698a9b46298ef65c4664924 else (if i < 6384 then 0x3ba58b1dd0c54dac14c77fae23340921de8d84ee762c77331536a8531df6b88cce248779b618019db400a398edf74c76c0a636a4529df4b88cff24c7713653bc9b09dbec9a00574b0020d5 else 0x3354921dfcd88ef262c778b1536f8531dae4d0efe5c47afad63350924002d86000122776b163bb18a9b7c298ed626877eae2334c921ddcd84eeb62c775315368c531df8b88cd2248777361)))) else (if i < 6504 then (if i < 6456 then (if i < 6432 then 0x3504629e4ce0ccd7248790b633c11931e0cc58f0786a781ba53c158a9e10c18c8b2866d70a63c29711aee494cd6248784b613be98b1df2c54de216c7812e63c0572991428e0026e50008a2 else 0x3c95b19e2ac9a00574b0020d53c38629a8c310f297066789253c71b21e48d8cf1462c7893153514629e50e0cdbb248791b633c6d8b1e34c54d4318a793b833368921e44d8cf1462c788b15) else (if i < 6480 then 0x800db1c00024cf2062c78fb1535b0629e18550f2c70666e9243c85b19e3cc58f1d62a6a08c53cadc199b8490f216c70033b68014731e2ae98d4718878c3853ca9c19b944d4dc024c78bb65 else 0x3cddb19e60c58f2f62a6a48c53cc9c199c2490f316c67953163ca58a9abe314f345ec799af5800dc1c0042ccc8c26466f9243cb5b19e4ac58f2462a6b60c53c34aa1e5ae0cf625aa66f124)) else (if i < 6552 then (if i < 6528 then 0x3d85689e9cc98f4c2ca7720c43d3dc19b66258f605a279dbb63cfa1b1e74e98f3d62c79e3153534629e80e0cf415ca6468a237b89319c8490f3f6c679b3163cd58a9a96314f38706671924 else 0x3e08529ece48cf926c47ca3613e35829f18c10f662467b68c43e2dc19f12d8cf6c1887c53833e21b19ef2294f875c47c2b613de0529f0cb88f846c27aa9763d5dd31a9c310f5d70678b895) else (if i < 6576 then 0x3e81711eec490f9f6c27ce4363e76129f36c14f9a6087b49233dec529f32b88f976c27bd0a53e61711f2cd84f9160a7c83043dcc5a1f02294f682467c9b623e55b09f1ec14f8e6087b90b4 else (if i < 6600 then 0x3dc0621f56e0cfad5c87b28a23e0c929f54d8cfa986c7d64053ea1829f4ec10f6b2467d33053e95821ed448cf6f1887d23833e89b19edc310fa37067d0b633e718a9f3cc14f642867be0a5 else 0x7ba8c43ec5c19efc254fb55a27ba0c43ec1c19efe254fb45a27b88c43ebdc19f00254fb35a27bb8c43eb9c19efa254fb25a27d4ba5))))))))) (i % 24)
def crossing (i : Nat) : Nat := field 49 (if i < 2016 then (if i < 1008 then (if i < 496 then (if i < 240 then (if i < 112 then (if i < 48 then (if i < 16 then 0x0 else (if i < 32 then 0x0 else 0x0)) else (if i < 80 then (if i < 64 then 0x0 else 0x2112f8c0b220608990805b140844be382c8804225f1c164402112f8e0b22010897c7099100844be384c8804225f1c264402212f8e14a2050897c709a1008e9902074820474c8103a41023a640a2520811d320512904000000000000000000000000) else (if i < 96 then 0xa112f8e13420608990809b142884be38530804225f1c1644000000000000010897c7059100844c0382e0804225f1c164402112f8e0b220508984705e1000000000000004225f1c16440c1132900b82810897c7059103044cc402e0a04225f1c1644 else 0x50947c605e102844be382d0814225f1c16840a112f8e0b420508980705c102844be382d0814225f1c16840a112f8c0b42050897c7059103044cc402e0a14225f1c16840a112f8c0b420608990805b142844be382d0814225f1c1684))) else (if i < 176 then (if i < 144 then (if i < 128 then 0x23a640a2520811d32051290408e9902894820474c8144a41023a640a2520811d32051290408e9902894820c021f1c5502000000000000011d32040e90408e990289482000000000000023a640a2520811d32051290408e9902894820474c8144a41 else 0x80272101944011097c70651008e9902874820474c8143a41023a640a1d20811d32050e90418043e38aa040c021f1c550206010f8e2a81011d32051290408e9902894820474c8144a41023a640a2520811d32051290408e9902894820474c8144a41) else (if i < 160 then 0x23ba4081d40811d36440ea0408e9902074820474c8103a41023a64081d20811d32040e90408e9902074820474c8103a4102212f8e0ca2030087c71140808e9902074820474c8103a41023a64081d20811d32040e904180442388a040c02201c45c2 else 0x23a64081d20811d39440e90408e9902074820474c8103a4102212f8c0ca2011d32040e90408e9902074820474c8103a41023a64081d20811e12040e9043064c840300a0474c8103a41023a64081d20811d32040e90408e9902074820474c8103a41)) else (if i < 208 then (if i < 192 then 0x23a64081d20800000000000008e990207482000000000000023a64081d20800000000000008e99020748200000000000002212f8e0ca2000000000000008e990207482000000000000023a64081d2080000000000000000000000000474c8103a41 else 0x23a64081d20811d32040e90408e9902074820474c8103a410c1132100b62811d32040e90408e9902074820474c8103a41023a64081d20811d32040e90408e9902074820474c8103a41023a640a2520800000000000018043e388a04000000000000) else (if i < 224 then 0x23a64081d20811d32040e9040844be382c880474c8103a41023a64081d20811d32040e90408e9902074820474c8103a41023a64081d20811d32040e90408e990289482000000000000023a64081d20811d32040e9043044c8402d8a14021f1c4542 else 0x23a640a2520811d32051290408e9902894820474c8144a41023a640a2520830087c7154080000000000000474c8103a41023a640a2520811d32040e90408e990207482000000000000023a64081d20830087c71140808e9902074820474c8103a41)))) else (if i < 368 then (if i < 304 then (if i < 272 then (if i < 256 then 0x23a640a1d20811d32050e90408e9902874820c021f1c550206010f8e2a81030087c71540808e9902894820474c8144a41023a640a2520811d32051290408e9902894820474c8144a41023a640a2520811d32051290408e9902894820474c8144a41 else 0x23a64081d20811d32040e9040844be382c880c021f1c4502023a64081d20811d32040e90408e9902074820474c8103a41023a64081d20811d32040e90408e9902074820c02211c45020601100e22e10608994805c140844be382c880474c8143a41) else (if i < 288 then 0x2112f8c0b22011d32040e90408e9902074820474c8103a41023a64081d20811e12040e9043044c8402d8a0474c8103a41023a64081d20811d32040e90408e990207482047748103a81023a6c881d40811d32040e90408e9902074820474c8103a41 else 0x23a64081d20800000000000008e990207482000000000000023a64081d20800000000000008e99020748200000000000000000000000000000000000000000000000000474c8103a41023a64081d20811d39440e90408e9902074820474c8103a41)) else (if i < 336 then (if i < 320 then 0x23a64081d20811d32040e90408e9902074820474c8103a4106010f8e2281000000000000008e9902074820474c8103a410000000000000608990805b143044c8402d8a000000000000023a64081d20800000000000018043e388a04000000000000 else 0x23a64081d20810897c70591008e9902074820474c8103a41023a64081d20811d32040e90408e9902074820474c8103a41023a64081d20811d32040e90408e9902074820474c8103a41023a64081d20811d32040e90408e9902074820474c8103a41) else (if i < 352 then 0x23a64061520811d32030a904180442386a040c02201c35c2080272101144010897c70591008e9902054820474c8102a41023a64081520811d32040a90418043e388a040c021f1c450206010f8e2281011d32040e90408e9902074820474c8103a41 else 0x23a64061520811d32030a90408e9901854820474c80c2a41023a64061520811dd2030aa0408e9b21855020474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a4102112f8e0b22030087c70d40808e9901854820474c80c2a41))) else (if i < 432 then (if i < 400 then (if i < 384 then 0x11d32030a90408e9901854820474e50c2a41023a64061520811d32030a9040844be302c880474c80c2a41023a64061520811d32030a90408f09018548214251f181784 else 0x2112f8e0b22030087c71140818043e388a040c021f1845020a032f8c23c1030087c71140818043e388a04000000000000023a64081d20811d32040e9040000000000000474c8103a410000000000000000000000000000000000000000000000000) else (if i < 416 then 0x23a64081d20811d32040e90408e99020748200000000000006010f8e2281030087c71140818043e388a0404225f181644000000000000010897c70591018043e388a040c021f1c450206010f8e2281030087c711408284a3e302f080c021f1c4502 else 0x23a64081d20811d32040e90408e9902074820474c8103a41023a64081d20811d32040e90408e9902074820474c8103a410a112f8e0b42010897c70591018043e388a040474c8103a41023a64081d20810897c70591008e9902074820474c8103a41)) else (if i < 464 then (if i < 448 then 0x23a64081d20811d32040e90408e9902074820474c8103a4102112f8e0b22011d32040e9040000000000000474c8103a41023a64081d20811d32040e90408e9902074820474c8103a4106010f8e2281011d32040e90408e99020748204225f1c1644 else 0x2112f8e0b22011d32040e90408e9902074820474c8103a41023a64081d20811d32040e90408e9902074820474c80c2a41000000000000011d32040e90408e9902074820474c8103a41023a64081d20830087c71140808e99020748204225f1c1644) else (if i < 480 then 0x11d32040e9042009c840651004750a103a4106010f8e2281011d32040e90408e9902074820474c8103a4106010f8e2281011d32040e90408e9902074820474c8103a4106010f8e2281030087c71140808e9902074820474c8103a41 else 0x23a64081d20850897c701a100844be380c8804225f1c064406010f8e2281011d32040e9040844be380c880474c8103a41023a64081d20811d32040e90408e9902074820474c8103a41023a64081d20830087c7114080000000000000474c8103a41))))) else (if i < 752 then (if i < 624 then (if i < 560 then (if i < 528 then (if i < 512 then 0xa010f8e22a1030087c71140808e9902074820474c8103a4102112f8e0322011d32040e90408e9902074820474c8103a41023a64081d20811d32040e90408e9902074820474c8103a41023a64081d20811d32040e9040844be300c88000000000000 else 0x6010f8e2281011d32040e9040844be380c880474c8103a41023a64081d20811d32040e90408e9902074820474c8103a41023a64081d20811d32040e90408e9902074820c021f1c4502000000000000050947c601e1008e99020748204225f1c0644) else (if i < 544 then 0x23a64081d20830087c71140808e9902074820474c8103a41023a64081d20811d32040e9040844be380c880474c8103a41023a64081d20811d32040e90408e990185482000000000000023a64081d20800000000000008e9902074820474c8103a41 else 0x23a64081d20811d32040e90408e9902074820474c8103a4106010f8e2281011d39430a9040000000000000474c8103a4106010f8e22e1030087c71140808e99020748204225f1c0644023a64081d20811d32040e90408e9902074820474c8103a41)) else (if i < 592 then (if i < 576 then 0x23a64081d20811d32040e9040000000000000474c8103a41000000000000011d32040e90408e9902894820c021f1c4502023a64081d20810897c70191008e9902074820474c8103a41023a64081d20811d32040e90408e9902074820474c8103a41 else 0xa010f8e23c1030087c71140808e9902074820474c8103a4102112f8e0322011d32040e90408e9902074820474c8103a41023a64081d20811d32040e90408e9902074820474c8103a41023a64081d20800000000000008e990185482000000000000) else (if i < 608 then 0x2112f8e0322011d32040e90408e9902074820474c8103a41023a64081d20830087c71140808e9902074820474c8103a41023a64081d20811d32040e90408e9902074820c021f18450206010f8e2281000000000000008e9902074820c021f1c5502 else 0x23a64081d20811d32040e90408e9902074820474c8103a41023a64081d20811d32040e90408e990185482000000000000023a64081d20811d32040e90408e9902074820474c8103a410a112f8e0342030087c71140808e9902074820474c8103a41))) else (if i < 688 then (if i < 656 then (if i < 640 then 0x23a64081d208108980701c1008e9902074820474c8103a41023a64081d20811d32040e90408e9902074820474c8103a4106010f8e2281011d32040e90408e9902074820474c8103a41023a64081d208300f8071140808eb1e2074820474c8103a41 else 0x23a64081d20811d32040e90408e9902074820474c8103a41023a64081d20830087c71140808e9902074820474c8103a410a112f8e0342010897c7019100844be380c880474c8103a41023a64081d20811d32040e90408e9902074820474c8103a41) else (if i < 672 then 0x6010f8e2281030087c7114082844c2380f080c021f1c450206010f8c2281050197c611e0818043e388a040c021f1c450206010f8e2281030087c71140818043e388a040c021f1c450206010f8e2281030087c7114082844be380d080474c8103a41 else 0x2112f8e0322010897c70191008e9902054820474c8102a41023a64081520811d32040a90408e9902054820c021f1c450202112f8e0322030087c71140818043e308a0414065f18478206010f8e2281011d32040a90408e9902054820c021f1c4502)) else (if i < 720 then (if i < 704 then 0x2112f8e0322010897c7019100844be380c880474c8102a41023a64081520811d32040a90408e9902054820474c8102a41023a64081520811d32040a90408e9902054820474c8102a41000000000000011e12040a90408e99020548214225f1c0684 else 0x23a64081520811d32040a9040844be380c880474c8102a41023a64081520811d32040a90408e9902054820474c8102a41023a64081520811d32040a90408e9902054820474c8102a41000000000000011d32040a9043044ca400e0a1822642006c5) else (if i < 736 then 0x23a64081520810897c70191008e9902054820474c8102a41023a64081520811d32040a90408e9902054820474c8102a41000000000000000000000000008e9902054820474c8102a41023a64081520800000000000008e990205482000000000000 else 0x2112f8e0322010897c70191008e9902054820474c8102a41023a64081520811d32040a90408e9902054820c021f1c450206010f8e2281030087c71140808e9902054820474c8102a41023a64081520811d32040a90408e9902054820474c8102a41)))) else (if i < 880 then (if i < 816 then (if i < 784 then (if i < 768 then 0x2112f8e032200000000000000844be380c8804225f1c06440c1132100362810897c70191008e9902054820474c8102a41023a64081520811d32040a90408e9902054820474c8102a4106010f8e2281011d32040a90408e99020548214225f1c0684 else 0x2112f8e0322050088c70de08280446386f040c02231c35c202112f8e0322010897c7019100844be380c881822652007050c113290038286089a0801c14300ec8384e1018226520070502112f8e0322010897c7019100844be380c8804225f1c0644) else (if i < 800 then 0x23a64061520811d32030a904180440386a040c02211c350202112f8e0322030088470d408180442306a0414066118378206010f8e1a81010897c701910180440386a0404225f1c06440601100e1ae1030088060d708280cc0306f040474c80c2a41 else 0x23a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a90418043e386a040474c80c2a41023a64061520800000000000008e9901854820474c80c2a41023a64061520810897c70191008e9901854820474c80c2a41)) else (if i < 848 then (if i < 832 then 0x23a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a4106010f8e1a81011d32030a90408e9901854820474c80c2a41023a64061520850897c701a1008ea981854820474c80c2a41 else 0x23a64061520810897c70191008e9901854820c021f1c350206010f8e1a81030087c60d408280cbe306f040c021f1c3502023a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41) else (if i < 864 then 0x23a64061520811d32030a90408e9901854820474c80c2a41000000000000011d32030a90408e9901854820474c80c2a81023a64061520811d32030a90408e9901854820c02211c35020a01100e1aa10608994801c140844be300c881822642006c5 else 0x23a64061520811d32030a90408e990185482000000000000023a64061520811d32030a90408e9901854820474c80c2a41023c64061540811d32030a90408e9901854820c021f1c3502023a64061520811d32030a90408e9901854820474c80c2a41))) else (if i < 944 then (if i < 912 then (if i < 896 then 0x23a64061540811d32030a90408e9901854820474c80c2a41023a64061520811d32030aa0408eeb21854820474c80c2a41023a74061540811d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a81 else 0x2112f8e0322011d32030a90408e99e1855020474ca0c2a81023a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41) else (if i < 928 then 0x23a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d52030aa0408e9981855020474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41023a64061540811d62030aa0408ea101855020474c80c2a41 else 0x23a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a410c1132100362811d32030a90418043e386a040474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41)) else (if i < 976 then (if i < 960 then 0x23a84061520811d32030a9040844be300c880474c80c2a41023a64061520811d32030a90408e9901854820474cf0c2a41023a65061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41 else 0x23ba4061520811d36430a90408e9901854820474c80c2a41023a64061520811d32030a90408e9901854820475480c2a41023a66061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e9901854820475880c2a41) else (if i < 992 then 0x23a64061520811d32030a90408ea101854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a9040844be300c880474c80c2a41 else 0x23a64061520811d33c30a90408e9981854820474c80c2a41023a65061520811d32030a90408e9901854820475880c2a41023a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d52030a90408e9901854820474c80c2a41)))))) else (if i < 1504 then (if i < 1248 then (if i < 1120 then (if i < 1056 then (if i < 1024 then 0x11d32030a90408e9ca1854820474c80c2a41023a64061520811e12030a90408e9901854820474d90c2a41023a64061520811d32030a90408e9901854820477480c2a41 else (if i < 1040 then 0x50947c801e1008453e300c880474c80c2a41023a64061520811d32030a90400000000000000000000000000000000000000000000000000000000000000474c80c2a410c1152100382810897c60191008e9901854820474c80c2a41 else 0x11d36430aa0408e9b21855020477590c2a81000000000000011d32030a90408e990185482000000000000023a64061520811d32030a9040000000000000000000000000000000000000000000000000000000000000000000000000)) else (if i < 1088 then (if i < 1072 then 0xa128f8a03c20608990801b1408e9901854820474c80c2a41023a64061520811d32030a9040000000000000474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41023a64061520800000000000008ee901855020477480c2a81 else 0x23a72861520811d32030a90408e9901854821822a41c0705023a64061520811d32030a90408ee901854820474d90c2a41023a64061520811d32030a9040000000000000474c80c2a41023a64061520811d32030a90408f0901854820478480c2a41) else (if i < 1104 then 0x23a64061520811d32030a90408e9b21854820474c80c2a41023a64061520811d32030a90408ee901854820474e50c2a41023a64061520811d32030a9040844be280c880474c80c2a41000000000000011d32030a90408e9901854820474c80c2a41 else 0x474c80c2a41))) else (if i < 1184 then (if i < 1152 then (if i < 1136 then 0x23a64061520811d32030a90408e9901854820477480c2a81023a6c861540811d32030a90408e9901854820474c80c2a41023a640615208608998801c143044cc400e0a0c021f1c350206010f8e1a81011d32030a90408e990185482000000000000 else 0x11d32030a90408e9901854820474e50c2a41023a64061520811d32030a90408e9901854821822a61c0705023a64061520811d32030a90408e9901854820474c80c2a41023c240615208608998801c1408e9901854820474c80c2a41) else (if i < 1168 then 0x2112f8e0322010897c7019100844c4380c8804225f1c064402112f8e0322010897c7019100844be380c88182265200705000000000000010897c70191018043e306a0404225f1c0644023a64061520810897c701910000000000000000000000000 else 0x2112f8c0322010897c6019100844be300c8804225f1806440221348c04a20608990801b1408453e300c8814235f18068402114f8c0322050947c601e1008483e300e0818326920080502112f8e0322010897c7019100844be380c8804225f1c0644)) else (if i < 1216 then (if i < 1200 then 0xc11528e0382811e12030a90408ee901855020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000844be300c8804225f180644 else 0xa12908c03c2011d36430aa04000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000844be300c88047848102a41000000000000011d32050a90400709040ca040038082065c2) else (if i < 1232 then 0x284a3e300f0814251f180784023a72861520850947c601e100000000000000474e50c2a41 else 0x23a64061520811d32030a90408e9901854820474c80c2a410601108e1a81030088070d408180440386b841004e4202288023a64081520811d32040a90408e9902054820474c8102a4106010f8e2281030087c71140818043e388a040474c8103a41)))) else (if i < 1376 then (if i < 1312 then (if i < 1280 then (if i < 1264 then 0x23c240615208509480601e1008e9901854820474c80c2a41023a64061520811d32030a90408e9901854820477480c2a81023a6c861540811d32030a90408e9901854820474c80c2a41023a64061520811d32030a9040844c0380e080c021f1c3502 else 0x8e9901854820474c80c2a41023a72861520811d32030a90408e9901854820474c80c2a410211300c0382011d32030a90408e9901854820474c80c2a41) else (if i < 1296 then 0x601100e1a81030088470d408180440386b8418226520070506010f8e2281030087c71140818043e388a040c021f1c450206010f8e2281000000000000018043e388a040c021f1c450206010f8e2281000000000000018043e388a040474c8102a41 else 0x6014f8c1a81030087c70d40818043e386a041402221c378206010f8e1a81030087c70d40818043e386a040c021f1c350206010f8e1a81030087c70d4080844be380c880c021f1c350206010f8e1a81030087c70d40818043e386a040c021f1c3502)) else (if i < 1344 then (if i < 1328 then 0xc021f18350206010f8c1a81030087c60d40818043e306a040c021f18350202112f8c0322030087c60d408280cbe306f0414031f18354202114f8c03220300f7c60d408284a3e300f080c03df1835c2 else 0x23a640615208000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000474c8081a410601f00c12e10000000000000000000000000000000000000) else (if i < 1360 then 0x2112f8c1322011097c60a5100884be30528814225f182684023a64061520811d32040e90408c9901854820474c8103a41023a64081d20811d32040e904000000000000000000000000023a64040d20860899481dc1418043e306a041422611c4784 else 0x2112f8c0b220108984605e103044ca382e0a04225f1416440c11320e0b62810897c6059100844be302c8804225f18164402112f8c0b42010897c6059100884be3032861832641c180302112f8c1322010897c6099100844be304c881822641c26c5))) else (if i < 1440 then (if i < 1408 then (if i < 1392 then 0x10897c6059103044ca382e0a04225f1816440c11330e0b82810897c6059100844be282c881822641c16c502112f8c0b22010897c6059100844be302c8804225f18164402112f8c0b220108980605c100844be302c8804225f181644 else 0xc11320e0b62850897c605a102844be302d081474c8103a410a212f8c0cc1860c99070600c2844be304d081822641c26c50c11320e1362810897c6059100844be302c8804225f1816440a112f8c0b41010897c6059100844be302c88042260181704) else (if i < 1424 then 0xa112f8c0b42050897c605a102844c2302f0814225f1816840c11330e0b82850897c605a102844be282d081822641c16c50a112f8c0b42050897c605a102844be302d0814225f1826840a112f8c13420608990709b142884be30530814225f181684 else 0x23a640a2520811d32051290408e9902894820474c8144a41023a640a2520811d32051290408e9902894820474c8144a41023a64081d20811d32040e9042844be302d080000000000000a128f8a0bc2050897c605a102844be302d08142260181704)) else (if i < 1472 then (if i < 1456 then 0x23a64081d20811d32040e90408e9902074820474c8103a41023a64081d20811d32040e90408e9902074820474c8144a41023a640a2520860c99070a01408e9902894820c021f185502023a640a2520811d32051290408e9902894820474c8144a41 else 0x23a640a2520811d32040e90408e9902074820474c8144a41023a64081d20811d32051290418043e308a0404425f182944023a64081d20811d32040e90408e9902074820474c8103a41023a64081d20811d32040e90408e99020748204425f182944) else (if i < 1488 then 0x2212f8c0ca2011d32040e90408e9902074820474c8103a41023a64081d20811097c60651008e9902074820474c8103a4102212f8c0ca2011d32050e90408e9902874820474c8103a41023a64081d20811d32040e90408e9902074820474c8144a41 else 0x23a64081d20811d32040e90418043e308a040474c8103a41023a64081d20811d32040e90408e9902074820474c8103a41023a64081d20851097c60661008ea982074820474c8103a41023a64081d20811d32040e90408e9902074820474c8103a41))))) else (if i < 1760 then (if i < 1632 then (if i < 1568 then (if i < 1536 then (if i < 1520 then 0x23a64081d20811d32040e90408e9902074820474c8103a41023a64081d20840139070ca200884be30328804425f18194402212f8c0ca2011d32040e90408e9902074820474c8103a41023a64081d20811d32040e90408e9902074820474c8103a41 else 0x23a64081d20811d32040e90408e99020748214425f18198402212f8a0ca2011e12040e90408e9902874820c021f184502023a64081d20800000000000008e9902074820474c8103a41023a64081d20811d32040e9040884be30328804425f181944) else (if i < 1552 then 0x23a64081d20811d32040e90408e9902074820474c8103a41023a64081d208300f8061140808eb1e2074820474c8103a41023a64081d20811d32040e90408e9902074820474c8103a41023a64081d20811097c60651008e9902074820474c8103a41 else 0x802720e1944011d32040e90408e9902074820474c8103a41023a64081d20811d32040e90408e9902074820474c8103a41023a64081d20830087c61140808e9902074820474c8103a41023a64081d20811d32040e90408e99020748204425f181944)) else (if i < 1600 then (if i < 1584 then 0x6010f8c2281030087c61140818043e308a040c021f18450206010f8c2281011097c60651018043e308a040c021f18450206010f8c2281030087c61140808e9902054820c021f184502023a64081d20811d32040e90408e9902074820474c8103a41 else 0x23a64061520830087c61140808e9902074820c021f184502000000000000011d32030a90408e990207482000000000000023a64081d20811d32040e9042884be30330804750a103a41023272861520860c9907060140000000000000464c80c2a41) else (if i < 1616 then 0x23a64081d20811d32051290408e9902074820474c80c2a41023a64081d20811932030a90408e9902074820474c8103a41023a64081d208608990709b1408e990207482000000000000023a64061520811d32030a90408e9901854821004e41c2288 else 0x11d32030a90428043e308a840474c8103a410a010f8c22a1011d32040e90408e9902074820474c8103a41023a64081d20840139070ca2008e9902074820474c8103a41023a64081d20811d32040e90408e9902074820474c8143a41))) else (if i < 1696 then (if i < 1664 then (if i < 1648 then 0xc02720e19e4011d32040e90408e9902074820474c8103a41023a64081d20811d32040e90408e9902074820474c8103a41023a640a2520811d32030a90408e9902074820464c80c2a41023a64081d20811d32040e90408e9902074820c021f1c4502 else 0x23a64081d20811d32040e90408e9902074820474c8144a41023a64061520800000000000008e9902074820474c80c2a41000000000000011d32030a9043009c83847900c021f184502023a64081d20811d32040e90408e9902074820474c8103a41) else (if i < 1680 then 0x23a64081d20811d32040e90418043e308a0404225f182644023a64081d20811d32040e90408e9902074820474c8103a41023a64081d20811d32040e90408e9902074820474c8103a41023a64081d20811d32040e90408e9902074820474c8103a41 else 0x23a64081d20811d32040e90408e9902074820474c8103a41023a64081d20811d32050e90408e9902874820474c8103a41023a640a2520811d32040e90408e9902074820474c8144a41023a640a2520811d32040e90408e9902074820474c8103a41)) else (if i < 1728 then (if i < 1712 then 0x23a64081d20811d32040e90408e9902074820474c8103a41023a64081d40811dd6440e90408e9902074820474c8103a41023a64081d20811d32040e9040844be302c880474c8103a41023a64081d20811d32040e90408e99020748204225f181644 else 0x23a64081d20811d32040e9040000000000000474c8103a41023a64081d20811d32040e90408e9902074820474c8103a41023a64081d20811d32040e90408e9902074820474c8103a41023a64081d20811d32040e90408e9902075020474c8103a41) else (if i < 1744 then 0xc11320e0b62811d32040e90418043e308a040474c8103a41023a64081d20811d32040e90408e9902074820474c8103a41023a64081d20811d32040e90408e9902074820474c8103a410c11320e0b62811d32040e9040000000000000474c8103a41 else 0x23a64081d20811d32040e90408e9902074820c03e0184502023ac7881d20811d32040e90408e9902074820474c8103a41023a64081d20811d32040e90408e9902074820474c8103a41023a64081d20811d32040e90408e9902074820474c8103a41)))) else (if i < 1888 then (if i < 1824 then (if i < 1792 then (if i < 1776 then 0x23a64081d20811d32040e90408e9902074820474c8103a41023a64081d20811d32040e90408e9902074820474c8103a4106010f8c2281011d32040e90408e9902074820474c8103a41023a64081d20811d32040e90408e9902074820474c8103a41 else 0x23264061520830087c61140818043e308a040c021f18450206010f8c2281030087c61140818043e288a041822641c16c506010f8c2281030087c61140808e9902054820c021f184502023a64081d20811d32040e90408e9902074820474c8103a41) else (if i < 1808 then 0x6010f8c2281011d32040e90408e9902074820474c8103a41023a64081d20811d32040e90408e9902074820474c8103a41023a64081d20811d32040e90408e9902074821822641c16c5023a85081d20811939430a9043044c8382d8a000000000000 else 0xc11320e0b628000000000000300ec8306e101822641c16c50c11320e0b6280000000000003044c8382d8a1822641c16c50c11320e0b628608990705b143844c8384e8a0474c80c2a4106010f8c2281000000000000008e9901854820474c8103a41)) else (if i < 1856 then (if i < 1840 then 0x23a64081d20811d32040e90408e9902074820474c8103a410c11320e0b62811d32040e90408e9902074820474c8143a41023a64081d2080000000000003044c8382d8a1822641c16c50802720e19440608990705b143044c8382d8a1822a4181705 else 0x23a64081d20811d32040e90408e9902074820474c8103a4102112f8c1322030087c61140808e9902074820474c8103a410000000000000608990705b143044ca382e0a0474c8103a410c11320e0b62811d32040e90408e9902074820474c8103a41) else (if i < 1872 then 0x23a64061520811d32030a90408e9901854820474c80c2a4102112f8c0b22011d32040a90408e9902054820474c8102a41023a64081520811d32040a90408e9902054820474c8103a41023a64081d20811d32040e90408e9902074820474c8103a41 else 0x23a64061520811d32030a90408e9901854820474c80c2a41023a64061540811dd6430a90408e9901854820474c80c2a41023a64061520811d32030a9040844be302c880474c80c2a41023a64061520811d32030a90408e99018548204225f181644))) else (if i < 1952 then (if i < 1920 then (if i < 1904 then 0x10897c50591008e990185482000000000000023a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e9901855020474c80c2a41 else 0x23a64061520830087c60d40808e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a9042844be302d0804754c0c2a41023a64061520811d32030a90408e9901854820474c80c2a41) else (if i < 1936 then 0xe11328e0bc2810897c6059100844be282c881c22641c174502112f8c0b22010897c60591008e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41 else 0x23a64081520830087c60d4080844be302c8804225f181644023a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e990185482000000000000023a64061520811d32030a90408e9901854820474c80c2a41)) else (if i < 1984 then (if i < 1968 then 0x23a64061520810897c60591008e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41023a64061520850897c605a100844be282c880478480c2a41 else 0x23a64061520810897c60591008e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a9040000000000000474c80c2a41023a64081d20850897c605a1008ea141854820474c80c2a41) else (if i < 2000 then 0x23a64061520810897c60591008e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a4102112f8c0b22011d32030a90408e9902074820c021f1c4502000000000000011d32020690418043e306a040474c80c2a41 else 0x2112f8a0b220608990705b140844be302c8804225f18164402112f8c0b22010897c60591018043e306a040c021f184502023264061520800897c60591018043e308a0408021f18450206010f8c2281000000000000008e9901854820474c80c2a41))))))) else (if i < 3024 then (if i < 2512 then (if i < 2256 then (if i < 2128 then (if i < 2064 then (if i < 2032 then 0x6010f8c1a81000000000000018043e306a040c021f18350206010f8c2281010897c6059100844c0302e0804225f18164402112f8a0b2200000000000000844be302c881822651c170502112f8c0b22010897c6059103044cc382e0a04225f181644 else (if i < 2048 then 0x23a64081d20811d32040e90418043e306a0400000000000006010f8e2281030087c60d408284a3e282f080c021f18350206010f8c1a81010897c60591018043e306a040c021f183502000000000000030087c50d408280cbe286f040c021f183502 else 0x23a64081d20830087c61140808e9902074820474c8103a41023a64081d20811d32040e90408e9902074820474c80c2a41023264061520811d32040e90408e9902074820474c8103a41023a64061520811d32040e90408c9901854820474c8103a41)) else (if i < 2096 then (if i < 2080 then 0x23264061520811d32040e90408e9902074820474c8103a41023a64061520810897c60591008e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c8103a41023264061520811d32040e90408e9902074820474c8103a41 else 0x23a64061520811d32030a9042009c83865100c021f184502023a64081d20811d32040e90408e9902074820474c8103a41023a64081d20811d32040e90408e9902074820474c8103a41023a64081d20811d32040e90408e9901854820474c8103a41) else (if i < 2112 then 0x23a64061520810897c60191008c9901854820474c8103a41023a64081d20811d32040e90418043e306a040474c80c2a41023a640615208401390708a2008e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41 else 0x23a64081d20811d32040e90408e9902074820474c8103a4102112f8c0322011932030a90408e9902074820474c8103a41023a64081d20811d32030a9040844be280c880474c80c2a4102112f8c0322011d32030a90408e9901854820474c80c2a41))) else (if i < 2192 then (if i < 2160 then (if i < 2144 then 0x23a64061520811d32030a90408e9901854820c021f184502023a64081d20811d32040e90408e9902074820474c8103a41023264061520811d32040e90408e9902074820474c8103a41023a64081d20850947c501e1018043e308a040474c8103a41 else 0x23a64081d20811d32040e90408e9902074820474c80c2a41023a64061520810897c60191008e9901854820474c80c2a41023a64061520811d32040e90408e9902074820474c8103a41023a64061520811d32040e9040844be300c880474c80c2a41) else (if i < 2176 then 0x23a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e9901854820c021f18450206010f8c22810108980601c1008e9902074820474c8103a41023a64081d20810897c601c1008e9902074820464c80c2a41 else 0x23a64081d20811d32040e90408e99020748214225f180784023a64081d20811932030a90408e9902074820474c8103a41023a64081d20811d32030a90408e9901854820474c80c2a41000000000000011d32040e9040844be280c8804225f180644)) else (if i < 2224 then (if i < 2208 then 0x23a64081d20811d32030a90408e99018548204225f180644023a64061520811d32030a90408e9901854820474c80c2a41023a64061520811932030a90408e9902074820474c8103a41023a64081d20830087c50d40818043e308a040c021f184502 else 0x6010f8c2281030087c61140810043e308a040c021f18450202112f8c0322011d32040e90408e9902074820474c8103a41023a64081d20811d32040e90408e9902074820474c8103a41023a64081d20811d32040e90408e9902074820474c80c2a41) else (if i < 2240 then 0x23a64081520811d32040a90408e9902054820474c8102a41023a64081520811d32040a90408e9902054820474c8102a41023a64081520830087c61140810043e308a040c021f18450206010f8c2281020087c61140818043e308a040c021f184502 else 0x23a64081520811d32040a90408e9902054820474c8102a41023a640815208608994701c142844be300d080474c8102a41023a64081520811d32040a90408e9902054820474c8102a41023a64081520810897c60191008e9902054820474c8102a41)))) else (if i < 2384 then (if i < 2320 then (if i < 2288 then (if i < 2272 then 0xc11320e0362810897c6019100844be300c8804225f18064402212f8c04a2060ca9470200c08e9902054820474c8102a41023a640815208608990701b143044ca380e0a0474c8102a41023a64081520800000000000008e9902054820474c8102a41 else 0x23a64061520811d32030a904100442306a040c02211835020401100c1ae1030088060d7083044c8380d8a04225f18064402112f8c0322010897c6019103044ca380e0a1004e41c22880402720e1144010897c6019103044c8380d8a04225f140644) else (if i < 2304 then 0xc19320e0401820087c60d40818043e306a040474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41 else 0x23a64061520811d32030a90408e9901854820477480c2a81023ba4061540811d36430aa0408e9b21855020474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e99018548204425f180943)) else (if i < 2352 then (if i < 2336 then 0xc11320e0362811d32030a90408e9901854820474c80c2a41023c24061520811d32030a90408e9901854821832641c0803023a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41 else 0x23a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e9901854820477590c2a41023a64061520811d32030a90408e9901854820474c80c2a41) else (if i < 2368 then 0x23a64061520810897c5025100844be2812880474c80c2a41000000000000011d32030a9040844be280c880474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41023a64061520811dd6430a90408e9901854820474c80c2a41 else 0x23a64061520811d32030a9040844be280c881822641c06c5023a64061520811d32030a9040000000000000474c80c2a41023a64061520811d32030a90408e9901854820474e50c2a41023a72861520811d32030a90408e9901854820474c80c2a41))) else (if i < 2448 then (if i < 2416 then (if i < 2400 then 0x23a64061520811d39430a90408e9901854820474c80c2a4102212f8a04a1811d32030a90408e990185482000000000000023a64061520811d32030a90408e9901854820478480c2a41023c2406152086089907020143044c838100a0474c80c2a41 else 0x23a64061520850897c501a103044c8380d8a04754c0c2a41023aa6061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a9040000000000000474c80c2a41023a64061520800000000000008e9901854820474c80c2a41) else (if i < 2432 then 0x23a64061520811d32030a90408e9901854820c021f1435020a032f8a1bc1011d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e990185482000000000000000000000000011d32030a90408e9901854820474c80c2a41 else 0x23a64061520811d32030a9043044cc380e0a0474c80c2a41023a64061520811d32030a90408e9901854821822661c0705023a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41)) else (if i < 2480 then (if i < 2464 then 0x23a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a81023a64061520811d32030a90408e9901854820474c80c2a41023a64061540811dd6430a90408e9901854820474c80c2a41 else 0x23a64061520811d32030a90408e9901854820474c80c2a41023a64061520830087c60d40808e9901854821822661c0705023a85061520811d32030a9040000000000000474c80c2a41000000000000011d32030a90408e9901854820474c80c2a41) else (if i < 2496 then 0x2212f8c04a2010897c6019100844be300c881822641c06c502212f8c04a2050897c6019100844be300c8804225f18064402212f8c04a2011097c60251008e9901854820474c80c2a41023a64061520810897c6019100884be3012880c021f183502 else 0x2112f8a032206089907020140844be300c8804225f18064402112f8c0322010897c6019100844be300c8804225f18064402112f8c0322010897c6019103044c8380d8a04225f18064402112f8c0322010897c6019100844be300c8804225f180644))))) else (if i < 2768 then (if i < 2640 then (if i < 2576 then (if i < 2544 then (if i < 2528 then 0x23a6c8615408601d90609c203044ca380e0a04225f18064402112f8c0322010897c6019100844be300c8804225f1806440c11320e0362810897c6019103044d238100a0000000000000211348a04a20000000000000300ec8304e1004225f140944 else 0x2112f8c0322011d32030a90408e9901854820474c80c2a410c11320e0362811d32030a90408e9901854820474c80c2a4102112f8c0322011d32030a904000000000000000000000000023a64061520811d32030a90408e9901854820474c80c2a41) else (if i < 2560 then 0x23a64061520811d32030a90408e99018548204225f18064406010f8c1a81011d32030a90408e9901854820474c80c2a41023a64061520811d32030a904180442306a040c02211835020601100c1ae1051d62030a9043044ca380e0a1475080c2a41 else 0x23a64061520811d32030a9040000000000000474c80c2a41023a64061520811e12030a9043044c8380d8a0474c80c2a41023a64061520811d32030a90408e9901854820477480c2a810a3ba4061520811d36430aa0408e9901854820474c80c2a41)) else (if i < 2608 then (if i < 2592 then 0x2112f8c0322011d32030a90408e9901854820474c80c2a410000000000000000000000000000000000000000000000000000000000000011d32030a90408e9901854820474e50c2a41023a64061520811d32030a9040844be280c8804225f140644 else 0x10897c60191008e99020548214225f14068402112f8c0322010897c60191008e9902054820474c8102a41023a64081520811dd6430a9043044ca380e0a1822651c070502112f8c0322030087c60d40818043e286a0414065f143782) else (if i < 2624 then 0xa112f8a03420608990701b1430454a300e0a0478480c2a4102112f8803220608a90601c1408f0901854820478480c2a4102114f8a03220000000000000304548380e0a04225f140644000000000000011e12030a9040844be280c881822641c06c5 else 0x23a64061520811d32030a90400000000000014225f180784023a6406152080000000000000000000000000474c80c2a41023a64061520811d32030a90408e9901854820477480c2a8102212f8c04a2050897c501a102844be300c881822661c0705))) else (if i < 2704 then (if i < 2672 then (if i < 2656 then 0x23a6406152080000000000000000000000000454c80c2a41022a64061520810897c60191008e9901854820474c80c2a41023a64061520810897c6019100844be300c880474c80c2a41023a64061520811d32030a904084a42300c880474c80c2a41 else 0x23ac7861520811d63c30a904284a3e280f0814251f14078402112f8c0322010897c6019100844be300c880474c80c2a41023a64061520811d32030a90408eeb21854821422611807840a11308c03c2010897c60191008e9901854820474c80c2a41) else (if i < 2688 then 0x23a64061520810897c601c1008e990185482000000000000000000000000011d32030a90408e9901854820474c80c2a41023a64061520800e03c7154082844be300c880c03e01835020601f00a1a810501c8050de080844be300c8804758f0c2a41 else 0x8e9901854820474c80c2a4102112f8c0322011d32030a90408e9901854820474c80c2a4102112f8c0322010897c60191008e9901854820474c80c2a41023a64061520810908060191008e9901854820474c80c2a41)) else (if i < 2736 then (if i < 2720 then 0x23a64061520811d32030a90408e99018548204225f180644023a64061520811d32030a90408e99018548204225f180644023a64061520811d32030a90408e99018548214251f14078402112f8c0322030087c60d40818043e286a0414065f143782 else 0x23a64061520811d32030a90408e990185482042260180704023a64061520811d32030a90408e9901854820474c80c2a410211300c0382011d32040a90408e9902054820474c8102a41023a64081520811d32040a90408e99020548204225f180644) else (if i < 2752 then 0x23a64061520811d32030a90408e9901854820474c80c2a81023a64061520811d32030a90408e9901854820474c80c2a41023a64061540811dd6430a90408e9901854820474c80c2a41023a64061520811d32030a9040844c0300e080474c80c2a41 else 0x23a64061520811d32030a90408e990185482042260180704023aa6061520811d32030a9040000000000000474c80c2a41000000000000011d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41)))) else (if i < 2896 then (if i < 2832 then (if i < 2800 then (if i < 2784 then 0x23a64061520811d32030a90408e9901854821004e41c22880211300a03820401390708a2008e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a90418043e306a040474c80c2a41 else 0x601500c1a81011d42830a90408e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a410a11300c03820108980501c1008f0901854820474c8102a4106010f8c1a81011d32030a9040000000000000474c80c2a41) else (if i < 2816 then 0x6010f8c1a81030087c60d40818043e306a040464c80c2a41023a64061520810897c60191008e9901854820474c80c2a41023a64061520811d32030a9040844be300c880474c80c2a41023a64061520811d32030a90418043e306a040474c80c2a41 else 0x23a64060d20811d32030690418043e306a040c021f14350206010f8c1a81030087c60d40818043e306a040c021f18350206010f8c1a81030087c60d40818043e306a0404225f18064406010f8c1a81030087c60d40818043e286a0414065f143782)) else (if i < 2864 then (if i < 2848 then 0x2112f8c0322030087c60d40818043e306a040c021f18350206010f8c1a81010897c601910280cbe288f040c021f18450206010f8c2281030087c61140818043e308a040c021f18450206010f8c1a81011d3203069040844be300c880474c80c1a41 else 0x6010f8c1a81030087c60d40818043e306a040c021f1835020a010f8c1aa1030198860d40828043e306f040c021f18350206010f8c1a81030087c60d40818043e306a0404225f18064406010f8c1a81050087c60d50818043e306a040c0969183502) else (if i < 2880 then 0xa010f8c1aa1030087c60d4082844be300d0814021f18354204014f8c1a81000000000000018043e286a040000000000000a032f8a1bc1030087c50d40818043e286a041822641c080506010f8c1a81030087c60d40818043e306a040c021f183502 else 0xa010f8c1aa1030087c60d4083044ca380e0a04225f1406440c11320e0362830087c60d40818043e306a040c021f1435020a032f8a1bc1030087c60d40818043e306a040c021f18350206010f8c1a81030087c60d40818043e306a040c021f183502))) else (if i < 2960 then (if i < 2928 then (if i < 2912 then 0xa032f8a1bc1030087c60d40818043e306a040c021f18350206010f8c1a81030087c60d40818043e306a040c03e018350202112f8a03220108a7c50191018043e308a040c021f18350206010f8c1a81000000000000018043e306a040c021f183502 else 0x6010f8c1a81030087c60d4082844be300d08000000000000023a64040d20811d3202069040000000000000474c8081a41023a64040d20811d32020690408e9901034820c02201825c202112f8c03220108980601c1018043e306a040c021f143502) else (if i < 2944 then 0x23a64040d208119320206904180442304a040c02211825020601100c12e10401390704a1c0844be300c880464c80c1a41023264060d20811932030690408c9901834820c021f18350206010f8c1a81011932830690418043e306a040c021f183502 else 0x23264040d20811932020690408c990103482046748081a8102326c840d40811936420690408e9901034820464c8081a41023a64040d20811932020690408c99010348204225f18064406010f8c1281011933020690408e9901034820464c8081a41)) else (if i < 2992 then (if i < 2976 then 0x11932020690408c9901034820464e5081a41023264040d2081193202069040844be280c880464c8081a41000000000000011932020690408c990103482046848081a410a128f8a03c2050947c501e1008c9901034820464c8081a41 else 0x2112f8a0322000000000000008c9ca10348204225f1406440c11320e0362810897c6019100000000000000c021f18350200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (if i < 3008 then 0x23a85061520811d42830a90408ea141854820464e5081a410a12900a03c2010897c501910284a3e280f080464e5081a410c11330e0382811939420690408c9ca10348214251f1007840c11320e0362850947c701e1008453e280c88000000000000 else 0x23a64081d20811d32040e90408e9902074820474c8103a41023a64081d20811d32040e9042844be300d081422601807040a11548a0341050897c6019103044cc380e0a14225f1406840c11320e0362830087c60d40808ea1418548204225f180644)))))) else (if i < 3520 then (if i < 3264 then (if i < 3136 then (if i < 3072 then (if i < 3040 then 0xc11328e03828608994701c140844be300c880474c8102a41023a64081520811d32040a90408e9902054820c021f18450206010f8c2281030087c61140818043e308a040474c8103a41023a64081d20811d32040e90408e9902074820474c8103a41 else (if i < 3056 then 0x23a6c861540811d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e99018548204225f18064406010f8c1a81011d32030a90408e9901854820474c80c2a41023a64061520811d32030a904180442306a040c02201835c2 else 0x23a64061520811d32030a9040844be280c880474c80c2a41023a64061520811d32030a9040000000000000474c80c2a41023a64061520811e12030a9043044c8380d8a0474c80c2a41023a64061520811d32030a90408e9901854820477480c2a81)) else (if i < 3104 then (if i < 3088 then 0x18043e306a04000000000000023a6406152080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000011d32030a90408e9901854820474e50c2a41 else 0x6010f8c1a81030087c60d40818043e306a040474c80c2a41023a64061520810897c60191008e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41) else (if i < 3120 then 0x6010f8c1281011d32020690408e9901034820474c8081a41023a64040d20811d320206904180442304a040c02201825c20802720e09440401390704a200844be300c880474c80c1a41023a64060d20811d32030690408e9901834820c021f183502 else 0xa128f8a03c2011d32020690408e9901034820474c8081a41023a64040d20811d32020690408e990103482047748081a81023a6c840d40811d32020690408e9901034820474c8081a41023a64040d20811d32020690408e99010348204225f180644))) else (if i < 3200 then (if i < 3168 then (if i < 3152 then 0x11d32020690408e9901034820474e5081a41023a64040d20811d3202069040844be280c880474c8081a41000000000000011d32020690408e990103482047848081a41 else 0x6010f8a1a81011d32030a90408e99018548200000000000006010f8c1a81030087c60d408284a3e280f0804225f18064406010f8c1a81030087c50d408280cbe286f040000000000000000000000000000000000000000000000000000000000000) else (if i < 3184 then 0x11d32020690408e9901034820474c8081a41023a64040d20811d3202069043044ca38ce0a000000000000023a64040d20811d32020690408e9901034820474c8081a41023a64040d20811d3202069043024ca38ae0a0474c80c1a41 else 0xc19320c0c01810897c5059100884be28328618326418180302112f8c1322010897c5099100844be284c881822641826c50c11320c13628608990609b140884be2852880c021f14250206014f8a12810206024715c1008e9901034820474c8081a41)) else (if i < 3232 then (if i < 3216 then 0xc11320c0b62850897c505a100844be282c8804225f1416440c11320c0b62810897c5059100844be282c880422601417040c11328c0b82810897c4059103044c8302d8a04225f14164402112f8a0b22010897c5059100844be282c8804425f141943 else 0x23a64081d20811d32040e90408c99020748214225f1416840a11300a0b82050897c505a103044cc302e0a14225f1416840a112f880b420608990605b142844be282d0814225f1416840a112f8a0b42050897c509a103044c8304d8a14425f142984) else (if i < 3248 then 0x2212f8a0ca2011097c50651008e9902074820474c8103a41023a64081d20811d32040e90408e9902074820474c8103a41023a64081d20830087c6114080884be2852880474c8103a41023a64061520811d32040e90408e9902074821004e4184288 else 0x23a64061520811932030a90408c9901854820464c80c2a41023264061520811932030a90408e9901854820474c80c2a4106010f8a2281011d32040e90408e9902074820474c8103a41023a64081d20811d32040e90408a9902074820474c8103a41)))) else (if i < 3392 then (if i < 3328 then (if i < 3296 then (if i < 3280 then 0x23a64081d20811d32040e90408e9902074820474c8103a41023a64081d20811d32040e90408e99020748204425f14194402212f8a0ca2011932030a90408c9901854820464c80c2a41023a64061520811932030a9040884be2832880464c80c2a41 else 0x2212f8a0ca2011d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41023a64061520860c99060601418043e288a040474c8103a41023a64081d20811d32040e90408e9902074820474c8103a41) else (if i < 3312 then 0x23a64081d20811d32030a9042009c83085100474c8103a41023a64061520830087c50d40808e9901854820474c80c2a410802720c1144011d32030a90408e9901854820c021f143502023a64061520811d32030a90408e9901854820474c80c2a41 else 0x23a64081d20811932030a90408e9902074820c021f184502023a64061520811d32040e90408e99018548214021f143542023a64061520811d32030a9042009c83045100474c80c2a41023a64061520811d32030a90408e9901854820464c80c2a41)) else (if i < 3360 then (if i < 3344 then 0x23a64061520811d32030a90408e9901854821804e41823c8023a64061520811d32030a90408e9901854820474c80c2a41023a64081d20830087c50d40808e9901854820474c80c2a41023a640615208601390608f2008e9901854820474c80c2a41 else 0x23a64081d20811d32040e90408e9902074820474c8103a41023a64081d20811d32040e90408e9902074820474c8103a41023a64081d20811d32040e90418043e308a040c021f144502023a64081d20811d32040e90408e99020748214021f143542) else (if i < 3376 then 0x23a64061520820087c51140818043e288a040474c8103a41023a64081d20811d32040e90408e9902074820474c8103a41023a64081d20811d32040e90408e9902074820474c8103a41023a64081d20811d32040e90408e9902074820474c8103a41 else 0x23a64081d20811d32040e9040844be282c8804225f141644023264061520811932030a90408c9901854820474c80c2a41023264061520811932030a90408c9901854820474c80c2a41023264061520811932030a90408c9901854820464c80c2a41))) else (if i < 3456 then (if i < 3424 then (if i < 3408 then 0xe11320c13a2811d32030a90418043e286a040474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e9901854820464c80c2a41 else 0xe11320c0ba28608990605b143044c8302e8a1822641816c50802720c19440608990605b143044c8302d8a1822a41417050c112f8c0b820608990605b143044c8302d8a1807641437080c11320c0b6286089906060143064c83030061822641826c5) else (if i < 3440 then 0xc11320c0b628608990605b143844c8304e8a0474c80c2a41023264061520811d32040e90408e9902074820c021f144502023a64081d20811d32040e90408e9902074820474c8103a41023a64081d20811d32040e90408e9902074821822641816c5 else 0x23a64061520811d32030a90408e9901854820474c80c2a41023a64081520810897c50991008e9902074820474c8103a410c11320c0b628608990605b142009c83065101822641816c50c11320c0b628608a90505c143044c8302d8a180764143708)) else (if i < 3488 then (if i < 3472 then 0x23a64061520811d32030a90408e9901854820474c80c2a41023a64061520811097c50650c3864c83030860474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41 else 0x23a64061520811532030a90408e9901854820474c80c2a41023a64061520810897c5059100844be282c880474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41) else (if i < 3504 then 0x23a640615208708990605d1408e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41 else 0x23a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e99018548204425f141944023a64061520811d32030a90408e9901854820474c80c2a41023a64040d20811d32030a90408e9901854820474c80c2a41))))) else (if i < 3776 then (if i < 3648 then (if i < 3584 then (if i < 3552 then (if i < 3536 then 0x2112f880b220608990605b140844be282c8804225f14164402112f8a0b22030087c50d4080044be282c880474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41 else 0x112f8a0b22030087c50d40818043e286a040c021f14350202112f8a0b22030087c50d40818043e286a040c021f14350204010f8a1a81050197c50de0818043e286a0404225f1416440211300a0b82010897c5059103044ca302e0a04225f141644) else (if i < 3568 then 0x23a64081d20830087c60d408284a3e282f080c021f18350206010f8c1a81010897c60591018043e306a040c021f1835020a032f8a1bc1030087c60d40818043e306a0404225f14164406010f8a1a81030087c50d408284a3e202f0814251f181784 else 0x23a64061520811d32030a9040884be2812861832641808030c192d820521811d32030a90408e9901854820474c8103a4106010f8a1a81011d32030a90408e9901854820474c80c2a41023a64061520840139060ca2008c9901854820474c8103a41)) else (if i < 3616 then (if i < 3600 then 0x2212f8a04a2060ca9460200c08e9901854820474c80c2a410802720c11440201390608a200884be2812881832a51808030c02720c11e4011097c5025100884be2812860804e41822880c19320c0401811d32030a90408e9901854820474c80c2a41 else 0x23a64061520811d32030a9043044c8300d8a1822641806c5023a64061520800000000000008e9901854820474c80c2a41000000000000011d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41) else (if i < 3632 then 0x222908a04a1811097c50251008e9901854820474c80c2a410c11328c03828608994601c140884be2012860478480c2a4102112f8803220608990601b140844be20128804225f1006440c11320c0362811e12030a90408e9901854820474c80c2a41 else 0x23a64061520811d32030a90408884028128604425f140944023a64061520811d32030a9040844be280c8804225f1406440011308a03c20108984501e1008e9901854820474c80c2a41022a64061520811532030a9040884be2812880474c80c2a41))) else (if i < 3712 then (if i < 3680 then (if i < 3664 then 0x23a64061520811d32030a9042009c83045100804e4182288023a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32040a90408e9901854820474c80c2a41 else 0x23a64061520811d32030a90408e9901854820454c80c2a41023a64061520811d32030a90408e9901854820422601407040211300a0382011d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41) else (if i < 3696 then 0x6010f8a1a81011097c50250c3064c830100608021f14350206010f8a1a81030087c50d40818043e286a0408021f14350206010f8a1a81020087c50d40828043e286a840c021f1435020a010f8a23c1030087c50d40810043e286a040c021f143502 else 0x4010f8a1a81030087c50d40818043e286a040c021f14350204010f8a1a81030087c50d4080844be280c8804225f14064406010f8a1a810608990601b1418043e206a041822641806c506010f8a1a81030087c50d40818043e286a040c021f143502)) else (if i < 3744 then (if i < 3728 then 0x23264060d20811932030690418043e286a040c021f14350206010f8a1a81020087c50d40818043e286a0404225f140644023a64040d20811d32020690408e99010348204225f140644023a64040d20811d32020690408e9901034820c021f143502 else 0x23a64040d20811d32020690408c9901034820464c8081a41023264040d2080000000000000844be200c880464c8081a41000000000000011932020690408c9901034820464c8081a41023264040d20811932020690408c99010348204225f140644) else (if i < 3760 then 0x23a64040d20811d32020690400000000000018226518078502112f8a0322010897c4019103044c8300e8a04225f14064402112f8a0322010897c50191008e9901034820464c8081a41023264040d20811d32020690408c9901034820464c8081a41 else 0x2112f8803220608990601b143064c830100604225f140644023264040d20811932020690408c99010348204225f140644023264040d20811932020690408c99010348204225f14064402112f880322011a1202069040844be280c880474c8081a41)))) else (if i < 3904 then (if i < 3840 then (if i < 3808 then (if i < 3792 then 0xc11320c0362810897c5019100844be280c881822651807050011328c038281193942069043044c8300d8a04225f14064402112f8a03220608998601c140044cc300e0a0464e5081a410c11320c0402810897c4019103044c8300d8a0464e5081a41 else 0x23a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41023a64081d20811d32040e90408e9901854820022601407040211300a0382000000000000000000000000004225f100644) else (if i < 3824 then 0x23a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41023a64061520811d32030a9043044c8300d8a0474c80c2a41000000000000011d32030a90408e990185482000000000000 else 0x6010f8a1a81030087c50d40818043e286a040c021f14350206010f8a1a81030087c40d4083044c8300d8a0c021f14350206010f8a1a81030087c50d40818043e286a040474c80c2a41023a64061520811d32030a90408e9901854820474c80c2a41)) else (if i < 3872 then (if i < 3856 then 0x2112f8a0322011d32030690408e9901834820474c80c1a41023a640615208608990601b142009c83045101822a41407050000000000000601d90509c203044c8300d8a0000000000000c11320c036281193942069043044c8300d8a000000000000 else 0x23a64040d20811d32020690408e9901034820474c8081a41023a64040d20811d32020690400000000000004225f100644023a64040d20800000000000008e9901034820474c8081a41023a64040d20811d32020690408e9901034820474c8081a41) else (if i < 3888 then 0x23a64040d2080000000000003844ca300f0a1c226518078502112f8a0322010897c4019103844c8300e8a04225f14064402112f8a0322010897c50191008e9901034820474c8081a41023a64040d20811d32020690408e9901034820474c8081a41 else 0x6010f8a1281000000000000018043e204a0414065f102782000000000000030087c50940800000000000004225f140644023a64040d20811d32020690408e99010348204225f100644023c24040d20810897c50191008e9901034820474c8081a41))) else (if i < 3968 then (if i < 3936 then (if i < 3920 then 0xc09328c2382811d3202069040000000000000474c8081a41023a64040d20811d32020690408e9901034821804e41813c804010f8a1a81030087c50d40828043e286a840474c80c2a41023a64061520811d32030a904284a3e200f0804225f140644 else 0x23a64040d20811d320206904103012288e08000000000000000000000000011d32020690408e9901034820474c8081a41023a64040d20800000000000008e9901034820474c8081a41023a64040d20811d3202069042009c83025100804e4181288) else (if i < 3952 then 0x23a64061520811d32030a90408c9901854820464c80c2a41023a64061520811d32030a90408c99018548204425f10194402212f880ca2011932030a9040844be202c881812641416c5023264020520811d32010290418043e204a0408029f142502 else 0x23a64040d20811d32020690408e9901034821c2264141745023a64061520811d32030a90408e9901854820474c80c2a41023a64061520840139050ca2008e9901854820474c80c2a410c11320a0b628008990505b1408e9901854820c021f103502)) else (if i < 4000 then (if i < 3984 then 0x2112f8603220608990501b1408c9901034820464c8081a4102212f8804a1860c99050210c08c9901034820464c8081a4104010f881a81030087c40d40808e9901854820474c80c2a4106010f8a1a81010897c4059100044be202c880474c8081a41 else 0x802720a11440604a90401c14304548280e04180764102708023264040d20811932020690410043e206a040c021f103502023a64061520811d32030a9040044c0200e080422601007040c11328a03828008994501c140844be180c881822641406c5) else (if i < 4016 then 0x402720a09440601390504f20284a3e180f0814251f14078402112f880322030087c409408280cbe204f040474c8081a41023a64040d20811d32020690408e99010348204425f1009430e19320a0421811d32020690408e9901034821822641406c5 else 0x10043e204a040c021f1025020a010f8812a1020087c4094082009c82825100804e4141288)))))))) (i % 16)
def cert : Certificate := ⟨bank,records,starts,edges⟩
end Finite4848.Audit.Simple.Compact

namespace Finite4848.Audit.Simple.Compact
open Matrix

def transitionCell (k lo hi r : Nat) : Bool :=
  if crossing r = 0 then check cert k lo hi r else true

def transitionBand (k lo hi start count : Nat) : Bool :=
  (List.range count).all (fun offset => transitionCell k lo hi (start+offset))

def TransitionRange (k lo hi start stop : Nat) : Prop :=
  ∀ r, start ≤ r → r < stop → transitionCell k lo hi r=true

theorem transitionFromBand {k lo hi start count : Nat}
    (h : transitionBand k lo hi start count=true) :
    TransitionRange k lo hi start (start+count) := by
  intro r small big
  have cell := List.all_eq_true.mp h (r-start) (List.mem_range.mpr (by omega))
  simpa only [show start+(r-start)=r by omega] using cell

theorem transitionJoin {k lo hi a b c : Nat}
    (first : TransitionRange k lo hi a b)
    (rest : TransitionRange k lo hi b c) :
    TransitionRange k lo hi a c := by
  intro r small big
  by_cases lt : r < b
  · exact first r small lt
  · exact rest r (by omega) big

theorem startPerm : basis.Perm (values cert 0) :=
  List.isPerm_iff.mp (by decide +kernel)
end Finite4848.Audit.Simple.Compact

namespace Finite4848.Audit.Cross
open Simple

structure Sole (xs : List Sig) (s : Sig) (p n : Nat) : Prop where
  pos : p < 8
  neg : n < 43
  off : goal.getLsbD n=false
  present : s∈xs
  active : separates p n s=true
  unique : ∀ w∈xs,separates p n w=true → w=s

def Blocked (xs : List Sig) :=
  ∃ a b : Sig,∃ p n na nb pa pb : Nat, a≠b ∧
    Sole xs a p na ∧ Sole xs b p nb ∧ Sole xs a pa n ∧ Sole xs b pb n

theorem gate_separates {p n : Nat} {u v : Sig} (op : Bool)
    (h : separates p n (gateWord op u v)=true) :
    separates p n u=true ∨ separates p n v=true := by
  cases op <;> cases a : u.getLsbD p <;> cases b : u.getLsbD n <;>
    cases c : v.getLsbD p <;> cases d : v.getLsbD n <;>
    simp [separates,gateWord,BitVec.getLsbD_and,BitVec.getLsbD_or,a,b,c,d] at h ⊢

def pass (u v z s : Sig) := if s=u ∨ s=v then z else s

theorem transfer {xs : List Sig} {s u v : Sig} {p n : Nat} (op : Bool)
    (su : u∈xs) (sv : v∈xs) (single : Sole xs s p n)
    (good : canSeparate (gateWord op u v :: discard xs u v)=true) :
    Sole (gateWord op u v :: discard xs u v) (pass u v (gateWord op u v) s) p n := by
  let z:=gateWord op u v
  let child:=z::discard xs u v
  have only : ∀ w∈child,separates p n w=true → w=pass u v z s := by
    intro w hw lit
    rcases List.mem_cons.mp hw with rfl|tail
    · rcases gate_separates op lit with left|right
      · have eq : u=s := single.unique u su left
        simp [pass,eq]
      · have eq : v=s := single.unique v sv right
        simp [pass,eq]
    · obtain ⟨old,excluded⟩:=List.mem_filter.mp tail
      have eq:=single.unique w old lit
      subst w
      obtain ⟨left,right⟩:=Bool.and_eq_true_iff.mp excluded
      have l : s≠u := by simpa using left
      have r : s≠v := by simpa using right
      simp [pass,l,r]
  obtain ⟨w,mem,lit⟩:=pairNecessary single.pos single.neg single.off good
  have eq:=only w mem lit
  exact ⟨single.pos,single.neg,single.off,eq ▸ mem,eq ▸ lit,only⟩

theorem cannot_merge {xs : List Sig} {a b : Sig} {p n na nb pa pb : Nat} {op : Bool}
    (dif : a≠b) (ap : Sole xs a p na) (bp : Sole xs b p nb)
    (an : Sole xs a pa n) (bn : Sole xs b pb n)
    (bothP : separates p na (gateWord op a b)=true)
    (bothN : separates pa n (gateWord op a b)=true) : False := by
  cases op
  · have pos := (Bool.and_eq_true_iff.mp bothN).1
    change (a &&& b).getLsbD pa=true at pos
    rw [BitVec.getLsbD_and] at pos
    have bP:=(Bool.and_eq_true_iff.mp pos).2
    have bN:=(Bool.and_eq_true_iff.mp bn.active).2
    have active : separates pa n b=true := Bool.and_eq_true_iff.mpr ⟨bP,bN⟩
    exact dif ((an.unique b bn.present active).symm)
  · have neg := (Bool.and_eq_true_iff.mp bothP).2
    change !(a ||| b).getLsbD na=true at neg
    rw [BitVec.getLsbD_or] at neg
    have bP:=(Bool.and_eq_true_iff.mp bp.active).1
    have bN : !(b.getLsbD na)=true := by
      simp at neg
      simp [neg.2]
    have active : separates p na b=true := Bool.and_eq_true_iff.mpr ⟨bP,bN⟩
    exact dif ((ap.unique b bp.present active).symm)

theorem propagate {xs : List Sig} {u v : Sig} (op : Bool) (hu : u∈xs) (hv : v∈xs)
    (fresh : gateWord op u v ∉ xs) (good : canSeparate (gateWord op u v :: discard xs u v)=true)
    (cut : Blocked xs) : Blocked (gateWord op u v :: discard xs u v) := by
  obtain ⟨a,b,p,n,na,nb,pa,pb,dif,ap,bp,an,bn⟩:=cut
  let z:=gateWord op u v
  have A:=transfer op hu hv ap good
  have B:=transfer op hu hv bp good
  have C:=transfer op hu hv an good
  have D:=transfer op hu hv bn good
  refine ⟨pass u v z a,pass u v z b,p,n,na,nb,pa,pb,?_,A,B,C,D⟩
  by_cases aa : a=u ∨ a=v <;> by_cases bb : b=u ∨ b=v
  · have A':=A.active
    have C':=C.active
    simp only [pass,aa,ite_true] at A' C'
    have identical : gateWord op u v=gateWord op a b := by
      rcases aa with rfl|rfl <;> rcases bb with rfl|rfl <;> first
        | contradiction
        | simp [gateWord,BitVec.or_comm,BitVec.and_comm]
    rw [identical] at A' C'
    exact False.elim (cannot_merge dif ap bp an bn A' C')
  · simp only [pass,aa,bb,ite_true,ite_false]
    intro old; apply fresh; change z∈xs; rw [old]; exact bp.present
  · simp only [pass,aa,bb,ite_true,ite_false]
    intro old; apply fresh; change z∈xs; rw [←old]; exact ap.present
  · simpa [pass,aa,bb] using dif

theorem goalPos (p : Nat) (hp : p < 8) : goal.getLsbD p=true := by
  have all : ∀ t : Fin 8,goal.getLsbD t.val=true := by decide +kernel
  exact all ⟨p,hp⟩

theorem no_goal {xs : List Sig} (cut : Blocked xs) : xs.contains goal=false := by
  obtain ⟨a,b,p,_,na,nb,_,_,dif,ap,bp,_,_⟩:=cut
  apply Bool.eq_false_iff.mpr
  intro got
  have mem:=List.contains_iff_mem.mp got
  have h1:=ap.unique goal mem (by simp [separates,goalPos p ap.pos,ap.off])
  have h2:=bp.unique goal mem (by simp [separates,goalPos p bp.pos,bp.off])
  exact dif (h1.symm.trans h2)

theorem size_remove {xs : List Sig} {a b : Sig} (nd : xs.Nodup) (ha : a∈xs) (hb:b∈xs) (ab:a≠b) :
    (discard xs a b).length+2=xs.length := by
  let rest:=xs.filter (fun w=>w != b)
  have ar : a∈rest := by simp [rest,ha,ab]
  have nr : rest.Nodup := nd.filter _
  have f:=filter_one b xs nd
  have s:=filter_one a rest nr
  simp only [hb,ar,ite_true] at f s
  change rest.length+1=xs.length at f
  change (rest.filter (fun w=>w != a)).length+1=rest.length at s
  have eqf : discard xs a b=rest.filter (fun w=>w != a) := by simp [rest,Simple.discard,List.filter_filter]
  rw [eqf]; omega

theorem excludes (k : Nat) {xs : List Sig} (nd : xs.Nodup) (tight : xs.length=k+1) (cut : Blocked xs) :
    search k xs=false := by
  induction k generalizing xs with
  | zero => exact no_goal cut
  | succ k ih =>
    have no:=no_goal cut
    apply Bool.eq_false_iff.mpr
    intro hit
    rcases Bool.or_eq_true_iff.mp hit with stop|more
    · change xs.contains goal=true at stop; rw [no] at stop; contradiction
    · obtain ⟨child,mem,yes⟩:=List.any_eq_true.mp more
      obtain ⟨a,ha,b,hb,lt,op,da,db,fresh,eq,sz,legal⟩:=explain mem
      have ne : a≠b := by intro e; rw [e] at lt; omega
      have del:=size_remove nd ha hb ne
      have bound:=chosen_length del op da db
      rw [eq] at sz legal yes
      have flags : da=true ∧ db=true := by
        cases da <;> cases db <;> simp [Bool.toNat] at bound ⊢ <;> omega
      obtain ⟨rfl,rfl⟩:=flags
      let z:=gateWord op a b
      have newZ : z∉xs := by
        intro old
        have yesZ := List.contains_iff_mem.mpr old
        change xs.contains z=false at fresh
        rw [yesZ] at fresh
        contradiction
      have nr : (discard xs a b).Nodup := nd.filter _
      have nz : z∉discard xs a b := fun hh=>newZ (List.mem_filter.mp hh).1
      have childN : (z::discard xs a b).Nodup := List.nodup_cons.mpr ⟨nz,nr⟩
      have childL : (z::discard xs a b).length=k+1 := by simp; omega
      have childC:=propagate op ha hb newZ legal cut
      have negative:=ih childN childL childC
      change search k (z::discard xs a b)=true at yes
      rw [negative] at yes; contradiction
end Finite4848.Audit.Cross

namespace Finite4848.Audit.Cross

def certifySole (xs : List Sig) (s : Sig) (p n : Nat) : Bool :=
  (((p < 8) && (n < 43)) && !goal.getLsbD n) &&
  (xs.contains s && separates p n s) &&
  xs.all (fun w=> !(separates p n w) || w==s)

theorem soleCertified {xs : List Sig} {s : Sig} {p n : Nat} (h : certifySole xs s p n=true) :
    Sole xs s p n := by
  obtain ⟨a,all⟩:=Bool.and_eq_true_iff.mp h
  obtain ⟨b,c⟩:=Bool.and_eq_true_iff.mp a
  obtain ⟨ran,off⟩:=Bool.and_eq_true_iff.mp b
  obtain ⟨pos,neg⟩:=Bool.and_eq_true_iff.mp ran
  obtain ⟨mem,active⟩:=Bool.and_eq_true_iff.mp c
  refine ⟨of_decide_eq_true pos,of_decide_eq_true neg,(by simpa using off),List.contains_iff_mem.mp mem,active,?_⟩
  intro w hw val
  have pass:=List.all_eq_true.mp all w hw
  simpa [val] using pass

def field6 (e i : Nat) := (e >>> (6*i)) &&& 63

def cutCheck (k : Nat) (xs : List Sig) (e : Nat) : Bool :=
  let p:=field6 e 0
  let n:=field6 e 1
  let a:=xs.getD (field6 e 2) 0
  let b:=xs.getD (field6 e 3) 0
  ((xs.length==k+1) && decide xs.Nodup) && (a != b) &&
    (certifySole xs a p (field6 e 4) && certifySole xs b p (field6 e 5)) &&
    (certifySole xs a (field6 e 6) n && certifySole xs b (field6 e 7) n)

theorem fromCheck {k : Nat} {xs : List Sig} {e : Nat} (ok : cutCheck k xs e=true) : search k xs=false := by
  obtain ⟨first,negative⟩:=Bool.and_eq_true_iff.mp ok
  obtain ⟨common,positive⟩:=Bool.and_eq_true_iff.mp first
  obtain ⟨shape,dif⟩:=Bool.and_eq_true_iff.mp common
  obtain ⟨len,nd⟩:=Bool.and_eq_true_iff.mp shape
  obtain ⟨a,b⟩:=Bool.and_eq_true_iff.mp positive
  obtain ⟨c,d⟩:=Bool.and_eq_true_iff.mp negative
  apply excludes k (of_decide_eq_true nd) (beq_iff_eq.mp len)
  exact ⟨_,_,_,_,_,_,_,_,by simpa using dif,soleCertified a,soleCertified b,soleCertified c,soleCertified d⟩
end Finite4848.Audit.Cross

namespace Finite4848.Audit.Simple.Compact
open Matrix

def cutCell (k r : Nat) : Bool :=
  if crossing r = 0 then true else Cross.cutCheck k (values cert r) (crossing r - 1)

def cutBand (k start count : Nat) : Bool :=
  (List.range count).all (fun offset => cutCell k (start+offset))

def CutRange (k start stop : Nat) : Prop :=
  ∀ r, start ≤ r → r < stop → cutCell k r=true

theorem cutFromBand {k start count : Nat} (h : cutBand k start count=true) :
    CutRange k start (start+count) := by
  intro r small big
  have cell := List.all_eq_true.mp h (r-start) (List.mem_range.mpr (by omega))
  simpa only [show start+(r-start)=r by omega] using cell

theorem cutJoin {k a b c : Nat}
    (first : CutRange k a b)
    (rest : CutRange k b c) :
    CutRange k a c := by
  intro r small big
  by_cases lt : r < b
  · exact first r small lt
  · exact rest r (by omega) big

end Finite4848.Audit.Simple.Compact

namespace Finite4848.Audit.Simple.Compact.MaskCut
open Matrix

def sigMask (ids : List Nat) : Nat := ids.foldr (fun j a=>a ||| (1<<<j)) 0
def columns (t : Nat) : Nat := (if t < 21 then (if t < 10 then (if t < 5 then (if t < 2 then (if t < 1 then 0x244111f900407800014504180fa07c0000404800c07d780000801480048007ff99f00008020050001ffbffffffff005c0000002011ffe1fffffff8020020800500000080000400002008414020000109000400a else 0x7f81204100407801219fff9fcfefffffffffe002807d000000051800040027ff9c000010000060001f7bffffffff0080040000402001000000901004014024060004000000000000001005800000020000a604c) else (if t < 3 then 0x437ffc30ca3454604a1fff43030a2ad0600a8080fe7e7ffffffffe022002418140840dfc005a8218082000e0096a10000262888c018210070226a080d3f009a821808918a180380c0300ffe04041042035c8a90 else (if t < 4 then 0x7f824020802040618c1fff9fcfcfffffffffe0841010220e0006200200028182408409fc00130018082000e0024c10000062080c0184100700c4c08893f03130218808180180380c0300ffe08082080021f0ce0 else 0x7fffffffffffffffffe0480202002080611300881010220e0210400240020184408409fc089c0218482000e1107011000060080c018810070407008093f001c0018008188180380c0300ffe1010410323900f00))) else (if t < 7 then (if t < 6 then 0x7f84808200782041f01fff9fefcfffffffffe010fd08000400278000080107fff5eefffffffffc1082102a4423800000044300084110000208f8001009843e000010000000001048400016000008000041ff000 else 0x7fffffffffffffffffe09004040050e0419c0220202053880338004080200308014700a14ce00001143c0081bc0002038000000001ffdd548f000000ffffffffc1210010c1082080022098000200003c7e00000) else (if t < 8 then 0x7fffffffffffffffffe1200808007c0001e008404040780003c000810080041001f000c00f0000021f800001c000041c0000000001ffe5fffffff8200200c00000010200001000008000e0020000003f8000000 else (if t < 9 then 0x401004100407800000400100fa0000000000000807d000000000000040007ff98000000000000001f7bffffffff000000000000000000000000000000000000000000000000000000000000000000000000000 else 0x2020020802040600000400202002080600000801010220e0000000200020180408409fc00000018082000e0000010000060080c018010070000008093f00000018008180180380c0300ffe0000000000000000)))) else (if t < 15 then (if t < 12 then (if t < 11 then 0x603006180607862000440120fa0208062000080907d220e04000002040207ffd88409fc100000181f7bffffffff18000060090c81a010071000008093f10000018008180180380c0340ffe404101f800000000 else 0x8040082007800000010001fa000000000000000f900000000000000080007ffe1eefffffffff800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (if t < 13 then 0xc0500c3007878800014001fafa0800000000000f97d0000080000000c0007fff9eefffffffff8201f7bffffffff20048004320ff80000000000000000000000000000000000000000000000000000000000000 else (if t < 14 then 0xa0600a2807840640010401fa200208064000080f910220e20000002080207ffe1eefffffffff81c082000e6000010000068080e01c010072000008093f60000018008180180390d0300ffe8081f80000000000 else 0x10100103e000000000008004040040e0000002002020430000000040002002000107000000000000103c0000000000038000000001ff980000000000ffffffff800000000000000000000000000000000000000))) else (if t < 18 then (if t < 16 then 0x14110143e0407900000480140fa040e080000200a07d430010000040042007ff99070100600000001f7fffffffff40038000040101ff981800000000ffffffff820000010400020003fc0000000000000000000 else (if t < 17 then 0x12120123e02040680000c006060060e0680002803030630e40000042002203a0418709fd80000018183c00e8000010038060080c01ff9807c0000080ffffffff81c0081a01a03c0c0380fff00fe000000000000 else 0x18140183e07900000010801fa40040e400000200f920430080000040082007ffe1effffffffff880103c0300000000038010100001ff986000000000ffffffff8800000408007fe000000000000000000000000)) else (if t < 19 then 0x1e1701e3e07979ee0014c01fafa0e0e4ee000280f97d630efc0000420c2207fff9effffffffff8bc1f7fffffffff7807807c3f0ff9ff987ff0000080ffffffff8bc0081f0da07fed03fefffc0fffdfc00000000 else (if t < 20 then 0x204001f8000000000001000808007c000000080040407800000000800080040001f00000000000001f8000000000001c0000000001ffe1fffffff80000000000000000000000000000000000000000000000000 else 0x224201f8802040700001400a0a007c807000088050507a0f00000082008205c041f409fe000000181fa000f00000101c0060080c01fff1fffffff8c093f8000001800c1801c0380e0300fffff00000000000000))))) else (if t < 32 then (if t < 26 then (if t < 23 then (if t < 22 then 0x284401fa007880000011001fa8007c0100000800f940781000000080088007ffe1fefffffffff8401f800c000000001c0080200001ffe1fffffff9001c000000000010000200400ff0000000000000000000000 else 0x305001fbe08000000001800c0c007ce200000a0060607b20000000c000a0060001f71000000000001fbc40000000001f8000000001fff9fffffffa00ffffffff840020200ffe000000000000000000000000000) else (if t < 24 then 0x3a5601fbe0f9c07c0011c01fae007ce77c000a80f9707b3fe00000c208a207ffe1fffffffffff8dc1fbc4ffe0000101f80f8380e01fff9fffffffbc0ffffffff8dc03c3e0ffe7feffb80ffffffffe0000000000 else (if t < 25 then 0x407ff80000000000001ffe400000000000000000fe7e7ffffffffe00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0x447ff84100407e00001ffe500fa3000000000000fe7f7ffffffffe04050007ff98000e00000000001f7bffffffff80092f000ff0000000000000000000000000000000000000000000000000000000000000000))) else (if t < 29 then (if t < 27 then 0x487ff882007e0000001ffe5fa00c000000000000ff7e7ffffffffe080a0007ffe1eeffffffffff00000030000000001257ffc000000000000000000000000000000000000000000000000000000000000000000 else (if t < 28 then 0x507ff903e3000000001ffe44040040f800000200fe7e7ffffffffe50002402000107200000000000103c8000000000039800000001ff998000000000fffffffff001c03ff000000000000000000000000000000 else 0x5c7ff9c3e37f7f80001ffe5fafafc0fc80000200ff7f7ffffffffe5c0f2407fff9efffffffffffa01f7fffffffffe01ffffffffffdff99f800000000fffffffffa01c03ffc007ff003ff0000000000000000000)) else (if t < 30 then 0x607ff9f80c000000001ffe4808007f0000000800fe7e7ffffffffea00088040001f04000000000001f8100000000001c6000000001ffe1fffffffc00e00000000001ffc00000000000000000000000000000000 else (if t < 31 then 0x787ff9fbefff8000001ffe5fac0c7fff00000a00ff7e7ffffffffef80aac07ffe1ffffffffffffc01fbdff000000001ffffff00001fff9ffffffff00fffffffffc01ffffffff7ffffc000000000000000000000 else 0x7f80000000000000001fff9fcfcfffffffffe0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))) else (if t < 37 then (if t < 34 then (if t < 33 then 0x7f980103f0000000001fff9fcfcfffffffffe300202043c000000040003002000107800000000000103e0000000000038000000001fffe0000000000fffffffffffe00000000000000000000000000000000000 else 0x7fe001fc00000000001fff9fcfcfffffffffec0040407c000000008000c0040001f80000000000001fc000000000001c0000000001ffffffffffffff00000000000000000000000000000000000000000000000) else (if t < 35 then 0x7ffffe0000000000001fffdfcfcffffffffff000fe7e7fffffffff000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else (if t < 36 then 0x7fffffffff800000001fffdfcfcfffffffffff00fe7e7ffffffffff00ffff60001fff000000000001fffc0000000001ff800000001ffffffffffffffffffffffffffffffffff800000000000000000000000000 else 0x7fffffffffffffffffe0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))) else (if t < 40 then (if t < 38 then 0x7fffffffffffffffffe600100ff0000000000000807f800000000000040007fffe000000000000001fffffffffffffe000000000000000000000000000000000000000000000000000000000000000000000000 else (if t < 39 then 0x7ffffffffffffffffff8001ff000000000000000ff80000000000000080007ffffffffffffffffffe00000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0x7fffffffffffffffffffffe00000000000000000fffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) else (if t < 41 then 0x7fffffffffffffffffffffffffff800000000000ffffffffffffffffff0007fffffffffffffffffffffffffffffffffffffffffffe0000000000000000000000000000000000000000000000000000000000000 else (if t < 42 then 0x7fffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))))))
def probe (k r : Nat) : Bool :=
  let e0:=crossing r
  if e0=0 then true else
    let e:=e0-1
    let ids:=digits 10 (records r)
    let pool:=sigMask ids
    let p:=Cross.field6 e 0
    let n:=Cross.field6 e 1
    let ai:=Cross.field6 e 2
    let bi:=Cross.field6 e 3
    let a:=ids.getD ai 0
    let b:=ids.getD bi 0
    let na:=Cross.field6 e 4
    let nb:=Cross.field6 e 5
    let pa:=Cross.field6 e 6
    let pb:=Cross.field6 e 7
    let pos:=pool &&& columns p
    let neg:=pool ^^^ (pool &&& columns n)
    let ka:=1<<<a
    let kb:=1<<<b
    ((ids.length==k+1) && decide (values cert r).Nodup) && (a != b) &&
    ((p < 8) && (pa < 8) && (pb < 8) && (8 ≤ n) && (n < 43) && (8 ≤ na) && (na < 43) && (8 ≤ nb) && (nb < 43)) &&
    (ai < ids.length) && (bi < ids.length) &&
    ((pos ^^^ (pos &&& columns na)) == ka) && ((pos ^^^ (pos &&& columns nb)) == kb) &&
    (neg &&& columns pa == ka) && (neg &&& columns pb == kb)
end Finite4848.Audit.Simple.Compact.MaskCut

namespace Finite4848.Audit.Simple.Compact.MaskCut
def ascIds : List Nat→Bool
  | a::b::tail => (a < b) && ascIds (b::tail)
  | _ => true
def probeIds (k r : Nat) : Bool :=
  let e0:=crossing r
  if e0=0 then true else
    let e:=e0-1
    let ids:=digits 10 (records r)
    let pool:=sigMask ids
    let p:=Cross.field6 e 0
    let n:=Cross.field6 e 1
    let ai:=Cross.field6 e 2
    let bi:=Cross.field6 e 3
    let a:=ids.getD ai 0
    let b:=ids.getD bi 0
    let na:=Cross.field6 e 4
    let nb:=Cross.field6 e 5
    let pa:=Cross.field6 e 6
    let pb:=Cross.field6 e 7
    let pos:=pool &&& columns p
    let neg:=pool ^^^ (pool &&& columns n)
    let ka:=1<<<a
    let kb:=1<<<b
    ((ids.length==k+1) && (ascIds ids && ids.all fun i=>i < 667)) && (a != b) &&
    ((p < 8) && (pa < 8) && (pb < 8) && (8 ≤ n) && (n < 43) && (8 ≤ na) && (na < 43) && (8 ≤ nb) && (nb < 43)) &&
    (ai < ids.length) && (bi < ids.length) &&
    ((pos ^^^ (pos &&& columns na)) == ka) && ((pos ^^^ (pos &&& columns nb)) == kb) &&
    (neg &&& columns pa == ka) && (neg &&& columns pb == kb)
end Finite4848.Audit.Simple.Compact.MaskCut

namespace Finite4848.Audit.Simple.Compact.MaskCut
open Matrix

def value (i : Nat) := (readWord bank i).val
def labelOK (i : Nat) := (List.range 43).all fun t=> (columns t).testBit i == (value i).getLsbD t
def nextOK (i : Nat) := decide ((value i).toNat < (value (i+1)).toNat)
abbrev Labels := ∀ i, i < 667 → labelOK i=true
abbrev Sorted := ∀ i, i < 666 → nextOK i=true

theorem label {i t : Nat} (hs : Labels) (hi : i < 667) (ht : t < 43) :
    (columns t).testBit i=(value i).getLsbD t :=
  beq_iff_eq.mp (List.all_eq_true.mp (hs i hi) t (List.mem_range.mpr ht))

theorem incr (hs : Sorted) {i j : Nat} (less : i < j) (top : j < 667) :
    (value i).toNat < (value j).toNat := by
  induction j with
  | zero => omega
  | succ j ih =>
    have step : (value j).toNat < (value (j+1)).toNat := of_decide_eq_true (hs j (by omega))
    by_cases eq : i=j
    · subst i; exact step
    · exact Nat.lt_trans (ih (by omega) (by omega)) step

theorem ordered : ∀ xs : List Nat, ascIds xs=true → xs.Pairwise (· < ·)
  | [],_ => .nil
  | [a],_ => by simp
  | a::b::tail,h => by
    obtain ⟨first,more⟩:=Bool.and_eq_true_iff.mp h
    have ab : a < b := of_decide_eq_true first
    have prev:=ordered (b::tail) more
    refine List.pairwise_cons.mpr ⟨?_,prev⟩
    intro j hj
    rcases List.mem_cons.mp hj with rfl|rest
    · exact ab
    · exact Nat.lt_trans ab ((List.pairwise_cons.mp prev).1 j rest)

theorem record_sorted (hs : Sorted) (ids : List Nat) (inc : ids.Pairwise (· < ·))
    (bound : ∀ j∈ids,j < 667) : Increasing (ids.map value) := by
  induction ids with
  | nil => exact .nil
  | cons a xs ih =>
    obtain ⟨first,rest⟩:=List.pairwise_cons.mp inc
    change List.Pairwise _ (value a :: xs.map value)
    refine List.pairwise_cons.mpr ⟨?_,ih rest (fun j hj=>bound j (List.mem_cons_of_mem _ hj))⟩
    intro w hw
    obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hw
    exact incr hs (first j hj) (bound j (List.mem_cons_of_mem _ hj))

theorem singletonBit (i j : Nat) : (1<<<i : Nat).testBit j=decide (i=j) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro b; exact decide_eq_true (oneShift b)
  · intro b; have eq:=of_decide_eq_true b; subst j
    simp [Nat.testBit_one_zero]

theorem presentBit (ids : List Nat) (j : Nat) : (sigMask ids).testBit j=decide (j∈ids) := by
  induction ids with
  | nil => simp [sigMask]
  | cons i rest ih =>
    change (sigMask rest ||| (1<<<i)).testBit j=_
    rw [Nat.testBit_or,singletonBit,ih]
    by_cases mem : j∈rest <;> by_cases eq : i=j <;> simp [mem,eq,Ne.symm,or_comm]

theorem selected (ids : List Nat) (hs : Labels) {p n a : Nat} (hp : p < 8) (hn : n < 43) (ng : goal.getLsbD n=false)
    (hbound : ∀ j∈ids,j < 667) (ha : a∈ids)
    (test : ∀ j∈ids, ((columns p).testBit j && !(columns n).testBit j) = decide (a=j)) :
    Cross.Sole (ids.map value) (value a) p n := by
  have agreeAt (j : Nat) (hj : j∈ids) : separates p n (value j)=decide (a=j) := by
    have t:=test j hj
    simpa only [label hs (hbound j hj) (by omega : p < 43),label hs (hbound j hj) hn,separates] using t
  refine ⟨hp,hn,ng,List.mem_map.mpr ⟨a,ha,rfl⟩,by simp [agreeAt a ha],?_⟩
  intro w mem sep
  obtain ⟨j,hj,rfl⟩:=List.mem_map.mp mem
  rw [agreeAt j hj] at sep
  exact congrArg value (of_decide_eq_true sep).symm

theorem solePass {xs : List Sig} {s : Sig} {p n : Nat} (h : Cross.Sole xs s p n) :
    Cross.certifySole xs s p n=true := by
  simp only [Cross.certifySole,h.pos,h.neg,decide_true,Bool.true_and,h.off,Bool.not_false,
    List.contains_iff_mem.mpr h.present,h.active,Bool.and_true]
  apply List.all_eq_true.mpr
  intro w mem
  by_cases lit : separates p n w=true
  · simp [lit,h.unique w mem lit]
  · simp [lit]

end Finite4848.Audit.Simple.Compact.MaskCut

namespace Finite4848.Audit.Simple.Compact.MaskCut
open Matrix

theorem leftMark (ids : List Nat) (p n a : Nat)
    (eq : (sigMask ids &&& columns p) ^^^ ((sigMask ids &&& columns p) &&& columns n)=1<<<a) :
    ∀ j∈ids,((columns p).testBit j && !(columns n).testBit j)=decide (a=j) := by
  intro j hj
  have h:=congrArg (fun x:Nat=>x.testBit j) eq
  change Nat.testBit (_ ^^^ _) j=(1<<<a : Nat).testBit j at h
  simp only [Nat.testBit_xor,Nat.testBit_and,presentBit,decide_eq_true hj,Bool.true_and,singletonBit] at h
  cases ep : (columns p).testBit j <;> cases en : (columns n).testBit j <;> simp [ep,en] at h ⊢ <;> assumption

theorem rightMark (ids : List Nat) (p n a : Nat)
    (eq : (sigMask ids ^^^ (sigMask ids &&& columns n)) &&& columns p=1<<<a) :
    ∀ j∈ids,((columns p).testBit j && !(columns n).testBit j)=decide (a=j) := by
  intro j hj
  have h:=congrArg (fun x:Nat=>x.testBit j) eq
  change Nat.testBit (_ &&& _) j=(1<<<a : Nat).testBit j at h
  simp only [Nat.testBit_xor,Nat.testBit_and,presentBit,decide_eq_true hj,Bool.true_and,singletonBit] at h
  cases ep : (columns p).testBit j <;> cases en : (columns n).testBit j <;> simp [ep,en] at h ⊢ <;> assumption

theorem goal_off (n : Nat) (hn : 8 ≤ n) : goal.getLsbD n=false := by
  change (2^8-1 : Nat).testBit n=false
  rw [Nat.testBit_two_pow_sub_one]
  exact decide_eq_false (by omega)

theorem fromProbe (labels : Labels) (sorted : Sorted) {k r : Nat} (h : probeIds k r=true) : cutCell k r=true := by
  by_cases stop : crossing r=0
  · simp [cutCell,stop]
  let e:=crossing r-1
  let ids:=digits 10 (records r)
  let p:=Cross.field6 e 0
  let n:=Cross.field6 e 1
  let ai:=Cross.field6 e 2
  let bi:=Cross.field6 e 3
  let a:=ids.getD ai 0
  let b:=ids.getD bi 0
  let na:=Cross.field6 e 4
  let nb:=Cross.field6 e 5
  let pa:=Cross.field6 e 6
  let pb:=Cross.field6 e 7
  let u:=sigMask ids &&& columns p
  let v:=sigMask ids ^^^ (sigMask ids &&& columns n)
  simp only [probeIds,stop,ite_false] at h
  change (((((((((ids.length==k+1) && (ascIds ids && ids.all fun i=>i < 667)) && (a != b)) &&
      ((p < 8) && (pa < 8) && (pb < 8) && (8 ≤ n) && (n < 43) && (8 ≤ na) && (na < 43) && (8 ≤ nb) && (nb < 43))) &&
      (ai < ids.length)) && (bi < ids.length)) &&
      ((u ^^^ (u &&& columns na)) == 1<<<a)) && ((u ^^^ (u &&& columns nb)) == 1<<<b)) &&
      (v &&& columns pa == 1<<<a) && (v &&& columns pb == 1<<<b))=true at h
  obtain ⟨h,hbn⟩:=Bool.and_eq_true_iff.mp h
  obtain ⟨h,han⟩:=Bool.and_eq_true_iff.mp h
  obtain ⟨h,hbp⟩:=Bool.and_eq_true_iff.mp h
  obtain ⟨h,hap⟩:=Bool.and_eq_true_iff.mp h
  obtain ⟨h,bok⟩:=Bool.and_eq_true_iff.mp h
  obtain ⟨h,aok⟩:=Bool.and_eq_true_iff.mp h
  obtain ⟨h,fields⟩:=Bool.and_eq_true_iff.mp h
  obtain ⟨shape,ne⟩:=Bool.and_eq_true_iff.mp h
  obtain ⟨len,attrs⟩:=Bool.and_eq_true_iff.mp shape
  obtain ⟨inc,valid⟩:=Bool.and_eq_true_iff.mp attrs
  have bounds (i : Nat) (hi : i∈ids) : i < 667 := of_decide_eq_true (List.all_eq_true.mp valid i hi)
  have nd:=increasing_nodup (record_sorted sorted ids (ordered _ inc) bounds)
  have atA : ai < ids.length := of_decide_eq_true aok
  have atB : bi < ids.length := of_decide_eq_true bok
  have elem (i : Nat) (hi : i < ids.length) : ids.getD i 0∈ids := by
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
  have gmap (i : Nat) (hi : i < ids.length) : (ids.map value).getD i 0=value (ids.getD i 0) := by
    simp [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem hi]
  have am : a∈ids := elem ai atA
  have bm : b∈ids := elem bi atB
  have diff : a≠b := by simpa using ne
  have dif : value a≠value b := by
    intro same
    have eq:=congrArg BitVec.toNat same
    rcases Nat.lt_or_gt_of_ne diff with lo|hi
    · have := incr sorted lo (bounds b bm); omega
    · have := incr sorted hi (bounds a am); omega
  simp only [Bool.and_eq_true,decide_eq_true_eq] at fields
  have hp : p < 8 := by omega
  have hpa : pa < 8 := by omega
  have hpb : pb < 8 := by omega
  have hna : na < 43 := by omega
  have hnb : nb < 43 := by omega
  have hn : n < 43 := by omega
  have s1:=selected ids labels hp hna (goal_off na (by omega)) bounds am (leftMark ids p na a (beq_iff_eq.mp hap))
  have s2:=selected ids labels hp hnb (goal_off nb (by omega)) bounds bm (leftMark ids p nb b (beq_iff_eq.mp hbp))
  have s3:=selected ids labels hpa hn (goal_off n (by omega)) bounds am (rightMark ids pa n a (beq_iff_eq.mp han))
  have s4:=selected ids labels hpb hn (goal_off n (by omega)) bounds bm (rightMark ids pb n b (beq_iff_eq.mp hbn))
  have rowEq : values cert r=ids.map value := by simp [values,signals,cert,ids,value,List.map_map]
  simp only [cutCell,stop,ite_false,rowEq,Cross.cutCheck]
  change (((((ids.map value).length==k+1) && decide (ids.map value).Nodup) &&
      ((ids.map value).getD ai 0 != (ids.map value).getD bi 0)) &&
      (Cross.certifySole (ids.map value) ((ids.map value).getD ai 0) p na &&
       Cross.certifySole (ids.map value) ((ids.map value).getD bi 0) p nb) &&
      (Cross.certifySole (ids.map value) ((ids.map value).getD ai 0) pa n &&
       Cross.certifySole (ids.map value) ((ids.map value).getD bi 0) pb n))=true
  simp only [gmap ai atA,gmap bi atB,List.length_map,len,decide_eq_true nd,Bool.true_and]
  change (value a != value b) && (Cross.certifySole (ids.map value) (value a) p na && Cross.certifySole (ids.map value) (value b) p nb) && (Cross.certifySole (ids.map value) (value a) pa n && Cross.certifySole (ids.map value) (value b) pb n)=true
  rw [solePass s1,solePass s2,solePass s3,solePass s4]
  simp [dif]

def fastBand (k first size : Nat) := (List.range size).all (fun j=>probeIds k (first+j))
theorem convertBand (L : Labels) (S : Sorted) {k first size : Nat} (yes : fastBand k first size=true) :
    cutBand k first size=true := by
  apply List.all_eq_true.mpr
  intro j hj
  exact fromProbe L S (List.all_eq_true.mp yes j hj)
end Finite4848.Audit.Simple.Compact.MaskCut

namespace Finite4848.Audit.Simple.Compact.MaskCut
def bankGood (i : Nat) := labelOK i && ((i==666) || nextOK i)
def bankBand (start len : Nat) := (List.range len).all fun z=>bankGood (start+z)
def BankRange (start finish : Nat) := ∀ i,start ≤ i → i < finish → bankGood i=true
theorem part {start len : Nat} (h : bankBand start len=true) : BankRange start (start+len) := by
  intro i l r
  have pass:=List.all_eq_true.mp h (i-start) (List.mem_range.mpr (by omega))
  simpa only [show start+(i-start)=i by omega] using pass
theorem bind {a b c : Nat} (x : BankRange a b) (y : BankRange b c) : BankRange a c := by
  intro i lo hi
  by_cases smaller : i < b
  · exact x i lo smaller
  · exact y i (by omega) hi

theorem goodLabels (x : BankRange 0 667) : Labels := by
  intro i hi
  exact (Bool.and_eq_true_iff.mp (x i (Nat.zero_le i) hi)).1
theorem goodSorted (x : BankRange 0 667) : Sorted := by
  intro i hi
  have val:=(Bool.and_eq_true_iff.mp (x i (Nat.zero_le i) (by omega))).2
  have ne : i≠666 := by omega
  simpa [ne] using val
end Finite4848.Audit.Simple.Compact.MaskCut

namespace Finite4848.Audit.Simple.Compact.MaskCut
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary0 : bankBand 0 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary16 : bankBand 16 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary32 : bankBand 32 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary48 : bankBand 48 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary64 : bankBand 64 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary80 : bankBand 80 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary96 : bankBand 96 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary112 : bankBand 112 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary128 : bankBand 128 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary144 : bankBand 144 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary160 : bankBand 160 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary176 : bankBand 176 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary192 : bankBand 192 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary208 : bankBand 208 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary224 : bankBand 224 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary240 : bankBand 240 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary256 : bankBand 256 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary272 : bankBand 272 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary288 : bankBand 288 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary304 : bankBand 304 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary320 : bankBand 320 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary336 : bankBand 336 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary352 : bankBand 352 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary368 : bankBand 368 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary384 : bankBand 384 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary400 : bankBand 400 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary416 : bankBand 416 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary432 : bankBand 432 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary448 : bankBand 448 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary464 : bankBand 464 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary480 : bankBand 480 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary496 : bankBand 496 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary512 : bankBand 512 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary528 : bankBand 528 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary544 : bankBand 544 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary560 : bankBand 560 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary576 : bankBand 576 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary592 : bankBand 592 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary608 : bankBand 608 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary624 : bankBand 624 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary640 : bankBand 640 16=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem dictionary656 : bankBand 656 11=true := by decide +kernel
theorem dictionaryAll : BankRange 0 667 := (bind (bind (bind (bind (bind (part dictionary0) (part dictionary16)) (bind (part dictionary32) (bind (part dictionary48) (part dictionary64)))) (bind (bind (part dictionary80) (part dictionary96)) (bind (part dictionary112) (bind (part dictionary128) (part dictionary144))))) (bind (bind (bind (part dictionary160) (part dictionary176)) (bind (part dictionary192) (bind (part dictionary208) (part dictionary224)))) (bind (bind (part dictionary240) (bind (part dictionary256) (part dictionary272))) (bind (part dictionary288) (bind (part dictionary304) (part dictionary320)))))) (bind (bind (bind (bind (part dictionary336) (part dictionary352)) (bind (part dictionary368) (bind (part dictionary384) (part dictionary400)))) (bind (bind (part dictionary416) (part dictionary432)) (bind (part dictionary448) (bind (part dictionary464) (part dictionary480))))) (bind (bind (bind (part dictionary496) (part dictionary512)) (bind (part dictionary528) (bind (part dictionary544) (part dictionary560)))) (bind (bind (part dictionary576) (bind (part dictionary592) (part dictionary608))) (bind (part dictionary624) (bind (part dictionary640) (part dictionary656)))))))
theorem labelsVerified : Labels := goodLabels dictionaryAll
theorem sortedVerified : Sorted := goodSorted dictionaryAll
end Finite4848.Audit.Simple.Compact.MaskCut

namespace Finite4848.Audit.Simple.Compact
open Matrix
def pp : List Nat := [0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 7, 7, 7, 7, 7]
def nn : List Nat := [18, 23, 28, 30, 33, 40, 18, 28, 35, 40, 42, 18, 23, 28, 30, 32, 38, 42, 10, 23, 35, 41, 18, 20, 40, 41, 9, 30, 35, 40, 42, 9, 28, 30, 32, 40, 42, 23, 30, 35, 40, 42]
def atPos (t : Nat) := pp.getD t 0
def atNeg (t : Nat) := nn.getD t 0
def packed (s : Sig) (ix : List Nat) : Nat := packRow s.getLsbD ix

theorem packed_bit (w : Sig) (ix : List Nat) (sz : ix.length=42) (t : Nat) :
    (packed w ix).testBit t=(decide (t < 42) && w.getLsbD (ix.getD t 0)) := by
  by_cases h : t < 42
  · have hi : t < ix.length := by omega
    have got : ix[t]?=some ix[t] := List.getElem?_eq_getElem hi
    have val : ix.getD t 0=ix[t] := by simp [List.getD_eq_getElem?_getD,got]
    simp only [decide_eq_true h,Bool.true_and,val,packed]
    exact pack_at _ _ _ _ got
  · simp only [decide_eq_false h,Bool.false_and,packed]
    exact pack_off _ _ _ (by omega)

def validBank (i : Nat) :=
  let w:=readWord bank i
  (w.pos==packed w.val pp) && (w.neg==packed w.val nn)

theorem allDigits (k x i : Nat) (mem : i∈digits k x) : i < 1024 := by
  induction k generalizing x with
  | zero => simp [digits] at mem
  | succ k ih =>
    simp only [digits] at mem
    split at mem
    · simp at mem
    · rcases List.mem_cons.mp mem with rfl|rest
      · have ht : x &&& 1023 ≤ 1023 := Nat.and_le_right
        omega
      · exact ih _ rest

theorem model {r : Nat} (checked : ∀ i : Fin 1024,validBank i.val=true) :
    Meaning (signals bank records r) atPos atNeg := by
  have poslen : pp.length=42 := by decide +kernel
  have neglen : nn.length=42 := by decide +kernel
  have pairBounds : ∀ j:Fin 42, atPos j < 8 ∧ atNeg j < 43 ∧ goal.getLsbD (atNeg j)=false := by decide +kernel
  refine ⟨(fun t ht=>pairBounds ⟨t,ht⟩),?_,?_⟩
  · intro w hw t
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hw
    have ok:=checked ⟨i,allDigits _ _ _ hi⟩
    obtain ⟨pos,_⟩:=Bool.and_eq_true_iff.mp ok
    exact (congrArg (fun a:Nat=>a.testBit t) (beq_iff_eq.mp pos)).trans (packed_bit _ _ poslen t)
  · intro w hw t
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hw
    have ok:=checked ⟨i,allDigits _ _ _ hi⟩
    obtain ⟨_,neg⟩:=Bool.and_eq_true_iff.mp ok
    exact (congrArg (fun a:Nat=>a.testBit t) (beq_iff_eq.mp neg)).trans (packed_bit _ _ neglen t)
end Finite4848.Audit.Simple.Compact

namespace Finite4848.Audit.Simple.Compact
set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
def bankPart (i : Nat) := (List.range 32).all (fun j=>validBank (i+j))
set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
theorem bankC0 : bankPart 0=true := by decide +kernel
set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
theorem bankC32 : bankPart 32=true := by decide +kernel
set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
theorem bankC64 : bankPart 64=true := by decide +kernel
set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
theorem bankC96 : bankPart 96=true := by decide +kernel
set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
theorem bankC128 : bankPart 128=true := by decide +kernel
set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
theorem bankC160 : bankPart 160=true := by decide +kernel
set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
theorem bankC192 : bankPart 192=true := by decide +kernel
set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
theorem bankC224 : bankPart 224=true := by decide +kernel
set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
theorem bankC256 : bankPart 256=true := by decide +kernel
set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
theorem bankC288 : bankPart 288=true := by decide +kernel
set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
theorem bankC320 : bankPart 320=true := by decide +kernel
set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
theorem bankC352 : bankPart 352=true := by decide +kernel
set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
theorem bankC384 : bankPart 384=true := by decide +kernel
set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
theorem bankC416 : bankPart 416=true := by decide +kernel
set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
theorem bankC448 : bankPart 448=true := by decide +kernel
set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
theorem bankC480 : bankPart 480=true := by decide +kernel
set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
theorem bankC512 : bankPart 512=true := by decide +kernel
set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
theorem bankC544 : bankPart 544=true := by decide +kernel
set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
theorem bankC576 : bankPart 576=true := by decide +kernel
set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
theorem bankC608 : bankPart 608=true := by decide +kernel
set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
theorem bankC640 : bankPart 640=true := by decide +kernel
set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
theorem bankC672 : bankPart 672=true := by decide +kernel
set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
theorem bankC704 : bankPart 704=true := by decide +kernel
set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
theorem bankC736 : bankPart 736=true := by decide +kernel
set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
theorem bankC768 : bankPart 768=true := by decide +kernel
set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
theorem bankC800 : bankPart 800=true := by decide +kernel
set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
theorem bankC832 : bankPart 832=true := by decide +kernel
set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
theorem bankC864 : bankPart 864=true := by decide +kernel
set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
theorem bankC896 : bankPart 896=true := by decide +kernel
set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
theorem bankC928 : bankPart 928=true := by decide +kernel
set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
theorem bankC960 : bankPart 960=true := by decide +kernel
set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
theorem bankC992 : bankPart 992=true := by decide +kernel
set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
theorem bankAt {i j:Nat} (ok : bankPart i=true) (lo : i ≤ j) (hi : j < i+32) : validBank j=true := by
  have pass:=List.all_eq_true.mp ok (j-i) (List.mem_range.mpr (by omega))
  simpa only [show i+(j-i)=j by omega] using pass
set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
theorem bank_verified (i : Fin 1024) : validBank i.val=true := by
  have bound:=i.isLt
  by_cases part0 : i.val < 32
  · exact bankAt bankC0 (by omega) (by omega)
  by_cases part32 : i.val < 64
  · exact bankAt bankC32 (by omega) (by omega)
  by_cases part64 : i.val < 96
  · exact bankAt bankC64 (by omega) (by omega)
  by_cases part96 : i.val < 128
  · exact bankAt bankC96 (by omega) (by omega)
  by_cases part128 : i.val < 160
  · exact bankAt bankC128 (by omega) (by omega)
  by_cases part160 : i.val < 192
  · exact bankAt bankC160 (by omega) (by omega)
  by_cases part192 : i.val < 224
  · exact bankAt bankC192 (by omega) (by omega)
  by_cases part224 : i.val < 256
  · exact bankAt bankC224 (by omega) (by omega)
  by_cases part256 : i.val < 288
  · exact bankAt bankC256 (by omega) (by omega)
  by_cases part288 : i.val < 320
  · exact bankAt bankC288 (by omega) (by omega)
  by_cases part320 : i.val < 352
  · exact bankAt bankC320 (by omega) (by omega)
  by_cases part352 : i.val < 384
  · exact bankAt bankC352 (by omega) (by omega)
  by_cases part384 : i.val < 416
  · exact bankAt bankC384 (by omega) (by omega)
  by_cases part416 : i.val < 448
  · exact bankAt bankC416 (by omega) (by omega)
  by_cases part448 : i.val < 480
  · exact bankAt bankC448 (by omega) (by omega)
  by_cases part480 : i.val < 512
  · exact bankAt bankC480 (by omega) (by omega)
  by_cases part512 : i.val < 544
  · exact bankAt bankC512 (by omega) (by omega)
  by_cases part544 : i.val < 576
  · exact bankAt bankC544 (by omega) (by omega)
  by_cases part576 : i.val < 608
  · exact bankAt bankC576 (by omega) (by omega)
  by_cases part608 : i.val < 640
  · exact bankAt bankC608 (by omega) (by omega)
  by_cases part640 : i.val < 672
  · exact bankAt bankC640 (by omega) (by omega)
  by_cases part672 : i.val < 704
  · exact bankAt bankC672 (by omega) (by omega)
  by_cases part704 : i.val < 736
  · exact bankAt bankC704 (by omega) (by omega)
  by_cases part736 : i.val < 768
  · exact bankAt bankC736 (by omega) (by omega)
  by_cases part768 : i.val < 800
  · exact bankAt bankC768 (by omega) (by omega)
  by_cases part800 : i.val < 832
  · exact bankAt bankC800 (by omega) (by omega)
  by_cases part832 : i.val < 864
  · exact bankAt bankC832 (by omega) (by omega)
  by_cases part864 : i.val < 896
  · exact bankAt bankC864 (by omega) (by omega)
  by_cases part896 : i.val < 928
  · exact bankAt bankC896 (by omega) (by omega)
  by_cases part928 : i.val < 960
  · exact bankAt bankC928 (by omega) (by omega)
  by_cases part960 : i.val < 992
  · exact bankAt bankC960 (by omega) (by omega)
  exact bankAt bankC992 (by omega) (by omega)
end Finite4848.Audit.Simple.Compact

namespace Finite4848.Audit.Simple.Compact
open Matrix

theorem fromCompactLayer {k a b c : Nat}
    (numerical : TransitionRange k b c a b)
    (cut : CutRange (k+1) a b)
    (next : ∀ q, b ≤ q → q < c → search k (values cert q)=false) :
    ∀ r, a ≤ r → r < b → search (k+1) (values cert r)=false := by
  intro r small big
  by_cases moves : crossing r=0
  · have step := numerical r small big
    simp only [transitionCell,moves,if_true] at step
    exact original_step (model bank_verified) step next
  · have stopped := cut r small big
    simp only [cutCell,moves,if_false] at stopped
    exact Cross.fromCheck stopped

theorem compact_conclude
    (t5 : TransitionRange 4 4022 4022 3940 4022) (c5 : CutRange 5 3940 4022)
    (t4 : TransitionRange 5 3940 4022 3189 3940) (c4 : CutRange 6 3189 3940)
    (t3 : TransitionRange 6 3189 3940 1350 3189) (c3 : CutRange 7 1350 3189)
    (t2 : TransitionRange 7 1350 3189 66 1350) (c2 : CutRange 8 66 1350)
    (t1 : TransitionRange 8 66 1350 1 66) (c1 : CutRange 9 1 66)
    (t0 : TransitionRange 9 1 66 0 1) (c0 : CutRange 10 0 1) :
    search 10 basis=false := by
  have solved6 (q : Nat) (h : 4022 ≤ q) (g : q < 4022) :
      search 4 (values cert q)=false := by omega
  have solved5 := fromCompactLayer t5 c5 solved6
  have solved4 := fromCompactLayer t4 c4 solved5
  have solved3 := fromCompactLayer t3 c3 solved4
  have solved2 := fromCompactLayer t2 c2 solved3
  have solved1 := fromCompactLayer t1 c1 solved2
  have solved0 := fromCompactLayer t0 c0 solved1
  exact (searchPerm 10 startPerm).trans (solved0 0 (by decide) (by decide))

end Finite4848.Audit.Simple.Compact

namespace Finite4848.Audit.Simple.Compact
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand0 : transitionBand 9 1 66 0 1=true := by decide +kernel
theorem transitionLayer0 : TransitionRange 9 1 66 0 1 :=
  (transitionFromBand transitionBand0)
end Finite4848.Audit.Simple.Compact

namespace Finite4848.Audit.Simple.Compact
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1 : transitionBand 8 66 1350 1 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand25 : transitionBand 8 66 1350 25 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand49 : transitionBand 8 66 1350 49 17=true := by decide +kernel
theorem transitionLayer1 : TransitionRange 8 66 1350 1 66 :=
  (transitionJoin (transitionFromBand transitionBand1) (transitionJoin (transitionFromBand transitionBand25) (transitionFromBand transitionBand49)))
end Finite4848.Audit.Simple.Compact

namespace Finite4848.Audit.Simple.Compact
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand66 : transitionBand 7 1350 3189 66 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand90 : transitionBand 7 1350 3189 90 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand114 : transitionBand 7 1350 3189 114 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand138 : transitionBand 7 1350 3189 138 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand162 : transitionBand 7 1350 3189 162 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand186 : transitionBand 7 1350 3189 186 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand210 : transitionBand 7 1350 3189 210 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand234 : transitionBand 7 1350 3189 234 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand258 : transitionBand 7 1350 3189 258 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand282 : transitionBand 7 1350 3189 282 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand306 : transitionBand 7 1350 3189 306 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand330 : transitionBand 7 1350 3189 330 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand354 : transitionBand 7 1350 3189 354 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand378 : transitionBand 7 1350 3189 378 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand402 : transitionBand 7 1350 3189 402 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand426 : transitionBand 7 1350 3189 426 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand450 : transitionBand 7 1350 3189 450 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand474 : transitionBand 7 1350 3189 474 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand498 : transitionBand 7 1350 3189 498 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand522 : transitionBand 7 1350 3189 522 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand546 : transitionBand 7 1350 3189 546 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand570 : transitionBand 7 1350 3189 570 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand594 : transitionBand 7 1350 3189 594 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand618 : transitionBand 7 1350 3189 618 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand642 : transitionBand 7 1350 3189 642 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand666 : transitionBand 7 1350 3189 666 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand690 : transitionBand 7 1350 3189 690 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand714 : transitionBand 7 1350 3189 714 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand738 : transitionBand 7 1350 3189 738 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand762 : transitionBand 7 1350 3189 762 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand786 : transitionBand 7 1350 3189 786 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand810 : transitionBand 7 1350 3189 810 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand834 : transitionBand 7 1350 3189 834 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand858 : transitionBand 7 1350 3189 858 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand882 : transitionBand 7 1350 3189 882 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand906 : transitionBand 7 1350 3189 906 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand930 : transitionBand 7 1350 3189 930 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand954 : transitionBand 7 1350 3189 954 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand978 : transitionBand 7 1350 3189 978 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1002 : transitionBand 7 1350 3189 1002 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1026 : transitionBand 7 1350 3189 1026 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1050 : transitionBand 7 1350 3189 1050 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1074 : transitionBand 7 1350 3189 1074 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1098 : transitionBand 7 1350 3189 1098 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1122 : transitionBand 7 1350 3189 1122 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1146 : transitionBand 7 1350 3189 1146 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1170 : transitionBand 7 1350 3189 1170 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1194 : transitionBand 7 1350 3189 1194 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1218 : transitionBand 7 1350 3189 1218 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1242 : transitionBand 7 1350 3189 1242 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1266 : transitionBand 7 1350 3189 1266 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1290 : transitionBand 7 1350 3189 1290 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1314 : transitionBand 7 1350 3189 1314 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1338 : transitionBand 7 1350 3189 1338 12=true := by decide +kernel
theorem transitionLayer2 : TransitionRange 7 1350 3189 66 1350 :=
  (transitionJoin (transitionJoin (transitionJoin (transitionJoin (transitionJoin (transitionFromBand transitionBand66) (transitionJoin (transitionFromBand transitionBand90) (transitionFromBand transitionBand114))) (transitionJoin (transitionFromBand transitionBand138) (transitionJoin (transitionFromBand transitionBand162) (transitionFromBand transitionBand186)))) (transitionJoin (transitionJoin (transitionFromBand transitionBand210) (transitionJoin (transitionFromBand transitionBand234) (transitionFromBand transitionBand258))) (transitionJoin (transitionJoin (transitionFromBand transitionBand282) (transitionFromBand transitionBand306)) (transitionJoin (transitionFromBand transitionBand330) (transitionFromBand transitionBand354))))) (transitionJoin (transitionJoin (transitionJoin (transitionFromBand transitionBand378) (transitionJoin (transitionFromBand transitionBand402) (transitionFromBand transitionBand426))) (transitionJoin (transitionJoin (transitionFromBand transitionBand450) (transitionFromBand transitionBand474)) (transitionJoin (transitionFromBand transitionBand498) (transitionFromBand transitionBand522)))) (transitionJoin (transitionJoin (transitionFromBand transitionBand546) (transitionJoin (transitionFromBand transitionBand570) (transitionFromBand transitionBand594))) (transitionJoin (transitionJoin (transitionFromBand transitionBand618) (transitionFromBand transitionBand642)) (transitionJoin (transitionFromBand transitionBand666) (transitionFromBand transitionBand690)))))) (transitionJoin (transitionJoin (transitionJoin (transitionJoin (transitionFromBand transitionBand714) (transitionJoin (transitionFromBand transitionBand738) (transitionFromBand transitionBand762))) (transitionJoin (transitionFromBand transitionBand786) (transitionJoin (transitionFromBand transitionBand810) (transitionFromBand transitionBand834)))) (transitionJoin (transitionJoin (transitionFromBand transitionBand858) (transitionJoin (transitionFromBand transitionBand882) (transitionFromBand transitionBand906))) (transitionJoin (transitionJoin (transitionFromBand transitionBand930) (transitionFromBand transitionBand954)) (transitionJoin (transitionFromBand transitionBand978) (transitionFromBand transitionBand1002))))) (transitionJoin (transitionJoin (transitionJoin (transitionFromBand transitionBand1026) (transitionJoin (transitionFromBand transitionBand1050) (transitionFromBand transitionBand1074))) (transitionJoin (transitionJoin (transitionFromBand transitionBand1098) (transitionFromBand transitionBand1122)) (transitionJoin (transitionFromBand transitionBand1146) (transitionFromBand transitionBand1170)))) (transitionJoin (transitionJoin (transitionFromBand transitionBand1194) (transitionJoin (transitionFromBand transitionBand1218) (transitionFromBand transitionBand1242))) (transitionJoin (transitionJoin (transitionFromBand transitionBand1266) (transitionFromBand transitionBand1290)) (transitionJoin (transitionFromBand transitionBand1314) (transitionFromBand transitionBand1338)))))))
end Finite4848.Audit.Simple.Compact

namespace Finite4848.Audit.Simple.Compact
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1350 : transitionBand 6 3189 3940 1350 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1374 : transitionBand 6 3189 3940 1374 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1398 : transitionBand 6 3189 3940 1398 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1422 : transitionBand 6 3189 3940 1422 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1446 : transitionBand 6 3189 3940 1446 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1470 : transitionBand 6 3189 3940 1470 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1494 : transitionBand 6 3189 3940 1494 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1518 : transitionBand 6 3189 3940 1518 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1542 : transitionBand 6 3189 3940 1542 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1566 : transitionBand 6 3189 3940 1566 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1590 : transitionBand 6 3189 3940 1590 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1614 : transitionBand 6 3189 3940 1614 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1638 : transitionBand 6 3189 3940 1638 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1662 : transitionBand 6 3189 3940 1662 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1686 : transitionBand 6 3189 3940 1686 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1710 : transitionBand 6 3189 3940 1710 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1734 : transitionBand 6 3189 3940 1734 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1758 : transitionBand 6 3189 3940 1758 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1782 : transitionBand 6 3189 3940 1782 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1806 : transitionBand 6 3189 3940 1806 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1830 : transitionBand 6 3189 3940 1830 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1854 : transitionBand 6 3189 3940 1854 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1878 : transitionBand 6 3189 3940 1878 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1902 : transitionBand 6 3189 3940 1902 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1926 : transitionBand 6 3189 3940 1926 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1950 : transitionBand 6 3189 3940 1950 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1974 : transitionBand 6 3189 3940 1974 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand1998 : transitionBand 6 3189 3940 1998 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2022 : transitionBand 6 3189 3940 2022 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2046 : transitionBand 6 3189 3940 2046 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2070 : transitionBand 6 3189 3940 2070 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2094 : transitionBand 6 3189 3940 2094 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2118 : transitionBand 6 3189 3940 2118 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2142 : transitionBand 6 3189 3940 2142 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2166 : transitionBand 6 3189 3940 2166 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2190 : transitionBand 6 3189 3940 2190 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2214 : transitionBand 6 3189 3940 2214 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2238 : transitionBand 6 3189 3940 2238 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2262 : transitionBand 6 3189 3940 2262 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2286 : transitionBand 6 3189 3940 2286 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2310 : transitionBand 6 3189 3940 2310 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2334 : transitionBand 6 3189 3940 2334 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2358 : transitionBand 6 3189 3940 2358 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2382 : transitionBand 6 3189 3940 2382 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2406 : transitionBand 6 3189 3940 2406 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2430 : transitionBand 6 3189 3940 2430 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2454 : transitionBand 6 3189 3940 2454 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2478 : transitionBand 6 3189 3940 2478 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2502 : transitionBand 6 3189 3940 2502 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2526 : transitionBand 6 3189 3940 2526 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2550 : transitionBand 6 3189 3940 2550 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2574 : transitionBand 6 3189 3940 2574 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2598 : transitionBand 6 3189 3940 2598 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2622 : transitionBand 6 3189 3940 2622 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2646 : transitionBand 6 3189 3940 2646 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2670 : transitionBand 6 3189 3940 2670 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2694 : transitionBand 6 3189 3940 2694 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2718 : transitionBand 6 3189 3940 2718 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2742 : transitionBand 6 3189 3940 2742 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2766 : transitionBand 6 3189 3940 2766 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2790 : transitionBand 6 3189 3940 2790 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2814 : transitionBand 6 3189 3940 2814 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2838 : transitionBand 6 3189 3940 2838 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2862 : transitionBand 6 3189 3940 2862 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2886 : transitionBand 6 3189 3940 2886 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2910 : transitionBand 6 3189 3940 2910 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2934 : transitionBand 6 3189 3940 2934 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2958 : transitionBand 6 3189 3940 2958 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand2982 : transitionBand 6 3189 3940 2982 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3006 : transitionBand 6 3189 3940 3006 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3030 : transitionBand 6 3189 3940 3030 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3054 : transitionBand 6 3189 3940 3054 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3078 : transitionBand 6 3189 3940 3078 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3102 : transitionBand 6 3189 3940 3102 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3126 : transitionBand 6 3189 3940 3126 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3150 : transitionBand 6 3189 3940 3150 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3174 : transitionBand 6 3189 3940 3174 15=true := by decide +kernel
theorem transitionLayer3 : TransitionRange 6 3189 3940 1350 3189 :=
  (transitionJoin (transitionJoin (transitionJoin (transitionJoin (transitionJoin (transitionJoin (transitionFromBand transitionBand1350) (transitionFromBand transitionBand1374)) (transitionJoin (transitionFromBand transitionBand1398) (transitionFromBand transitionBand1422))) (transitionJoin (transitionJoin (transitionFromBand transitionBand1446) (transitionFromBand transitionBand1470)) (transitionJoin (transitionFromBand transitionBand1494) (transitionJoin (transitionFromBand transitionBand1518) (transitionFromBand transitionBand1542))))) (transitionJoin (transitionJoin (transitionJoin (transitionFromBand transitionBand1566) (transitionFromBand transitionBand1590)) (transitionJoin (transitionFromBand transitionBand1614) (transitionJoin (transitionFromBand transitionBand1638) (transitionFromBand transitionBand1662)))) (transitionJoin (transitionJoin (transitionFromBand transitionBand1686) (transitionFromBand transitionBand1710)) (transitionJoin (transitionFromBand transitionBand1734) (transitionJoin (transitionFromBand transitionBand1758) (transitionFromBand transitionBand1782)))))) (transitionJoin (transitionJoin (transitionJoin (transitionJoin (transitionFromBand transitionBand1806) (transitionFromBand transitionBand1830)) (transitionJoin (transitionFromBand transitionBand1854) (transitionFromBand transitionBand1878))) (transitionJoin (transitionJoin (transitionFromBand transitionBand1902) (transitionFromBand transitionBand1926)) (transitionJoin (transitionFromBand transitionBand1950) (transitionJoin (transitionFromBand transitionBand1974) (transitionFromBand transitionBand1998))))) (transitionJoin (transitionJoin (transitionJoin (transitionFromBand transitionBand2022) (transitionFromBand transitionBand2046)) (transitionJoin (transitionFromBand transitionBand2070) (transitionJoin (transitionFromBand transitionBand2094) (transitionFromBand transitionBand2118)))) (transitionJoin (transitionJoin (transitionFromBand transitionBand2142) (transitionFromBand transitionBand2166)) (transitionJoin (transitionFromBand transitionBand2190) (transitionJoin (transitionFromBand transitionBand2214) (transitionFromBand transitionBand2238))))))) (transitionJoin (transitionJoin (transitionJoin (transitionJoin (transitionJoin (transitionFromBand transitionBand2262) (transitionFromBand transitionBand2286)) (transitionJoin (transitionFromBand transitionBand2310) (transitionFromBand transitionBand2334))) (transitionJoin (transitionJoin (transitionFromBand transitionBand2358) (transitionFromBand transitionBand2382)) (transitionJoin (transitionFromBand transitionBand2406) (transitionJoin (transitionFromBand transitionBand2430) (transitionFromBand transitionBand2454))))) (transitionJoin (transitionJoin (transitionJoin (transitionFromBand transitionBand2478) (transitionFromBand transitionBand2502)) (transitionJoin (transitionFromBand transitionBand2526) (transitionJoin (transitionFromBand transitionBand2550) (transitionFromBand transitionBand2574)))) (transitionJoin (transitionJoin (transitionFromBand transitionBand2598) (transitionFromBand transitionBand2622)) (transitionJoin (transitionFromBand transitionBand2646) (transitionJoin (transitionFromBand transitionBand2670) (transitionFromBand transitionBand2694)))))) (transitionJoin (transitionJoin (transitionJoin (transitionJoin (transitionFromBand transitionBand2718) (transitionFromBand transitionBand2742)) (transitionJoin (transitionFromBand transitionBand2766) (transitionJoin (transitionFromBand transitionBand2790) (transitionFromBand transitionBand2814)))) (transitionJoin (transitionJoin (transitionFromBand transitionBand2838) (transitionFromBand transitionBand2862)) (transitionJoin (transitionFromBand transitionBand2886) (transitionJoin (transitionFromBand transitionBand2910) (transitionFromBand transitionBand2934))))) (transitionJoin (transitionJoin (transitionJoin (transitionFromBand transitionBand2958) (transitionFromBand transitionBand2982)) (transitionJoin (transitionFromBand transitionBand3006) (transitionJoin (transitionFromBand transitionBand3030) (transitionFromBand transitionBand3054)))) (transitionJoin (transitionJoin (transitionFromBand transitionBand3078) (transitionFromBand transitionBand3102)) (transitionJoin (transitionFromBand transitionBand3126) (transitionJoin (transitionFromBand transitionBand3150) (transitionFromBand transitionBand3174))))))))
end Finite4848.Audit.Simple.Compact

namespace Finite4848.Audit.Simple.Compact
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3189 : transitionBand 5 3940 4022 3189 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3213 : transitionBand 5 3940 4022 3213 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3237 : transitionBand 5 3940 4022 3237 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3261 : transitionBand 5 3940 4022 3261 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3285 : transitionBand 5 3940 4022 3285 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3309 : transitionBand 5 3940 4022 3309 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3333 : transitionBand 5 3940 4022 3333 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3357 : transitionBand 5 3940 4022 3357 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3381 : transitionBand 5 3940 4022 3381 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3405 : transitionBand 5 3940 4022 3405 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3429 : transitionBand 5 3940 4022 3429 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3453 : transitionBand 5 3940 4022 3453 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3477 : transitionBand 5 3940 4022 3477 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3501 : transitionBand 5 3940 4022 3501 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3525 : transitionBand 5 3940 4022 3525 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3549 : transitionBand 5 3940 4022 3549 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3573 : transitionBand 5 3940 4022 3573 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3597 : transitionBand 5 3940 4022 3597 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3621 : transitionBand 5 3940 4022 3621 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3645 : transitionBand 5 3940 4022 3645 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3669 : transitionBand 5 3940 4022 3669 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3693 : transitionBand 5 3940 4022 3693 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3717 : transitionBand 5 3940 4022 3717 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3741 : transitionBand 5 3940 4022 3741 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3765 : transitionBand 5 3940 4022 3765 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3789 : transitionBand 5 3940 4022 3789 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3813 : transitionBand 5 3940 4022 3813 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3837 : transitionBand 5 3940 4022 3837 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3861 : transitionBand 5 3940 4022 3861 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3885 : transitionBand 5 3940 4022 3885 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3909 : transitionBand 5 3940 4022 3909 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3933 : transitionBand 5 3940 4022 3933 7=true := by decide +kernel
theorem transitionLayer4 : TransitionRange 5 3940 4022 3189 3940 :=
  (transitionJoin (transitionJoin (transitionJoin (transitionJoin (transitionJoin (transitionFromBand transitionBand3189) (transitionFromBand transitionBand3213)) (transitionJoin (transitionFromBand transitionBand3237) (transitionFromBand transitionBand3261))) (transitionJoin (transitionJoin (transitionFromBand transitionBand3285) (transitionFromBand transitionBand3309)) (transitionJoin (transitionFromBand transitionBand3333) (transitionFromBand transitionBand3357)))) (transitionJoin (transitionJoin (transitionJoin (transitionFromBand transitionBand3381) (transitionFromBand transitionBand3405)) (transitionJoin (transitionFromBand transitionBand3429) (transitionFromBand transitionBand3453))) (transitionJoin (transitionJoin (transitionFromBand transitionBand3477) (transitionFromBand transitionBand3501)) (transitionJoin (transitionFromBand transitionBand3525) (transitionFromBand transitionBand3549))))) (transitionJoin (transitionJoin (transitionJoin (transitionJoin (transitionFromBand transitionBand3573) (transitionFromBand transitionBand3597)) (transitionJoin (transitionFromBand transitionBand3621) (transitionFromBand transitionBand3645))) (transitionJoin (transitionJoin (transitionFromBand transitionBand3669) (transitionFromBand transitionBand3693)) (transitionJoin (transitionFromBand transitionBand3717) (transitionFromBand transitionBand3741)))) (transitionJoin (transitionJoin (transitionJoin (transitionFromBand transitionBand3765) (transitionFromBand transitionBand3789)) (transitionJoin (transitionFromBand transitionBand3813) (transitionFromBand transitionBand3837))) (transitionJoin (transitionJoin (transitionFromBand transitionBand3861) (transitionFromBand transitionBand3885)) (transitionJoin (transitionFromBand transitionBand3909) (transitionFromBand transitionBand3933))))))
end Finite4848.Audit.Simple.Compact

namespace Finite4848.Audit.Simple.Compact
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3940 : transitionBand 4 4022 4022 3940 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3964 : transitionBand 4 4022 4022 3964 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand3988 : transitionBand 4 4022 4022 3988 24=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem transitionBand4012 : transitionBand 4 4022 4022 4012 10=true := by decide +kernel
theorem transitionLayer5 : TransitionRange 4 4022 4022 3940 4022 :=
  (transitionJoin (transitionJoin (transitionFromBand transitionBand3940) (transitionFromBand transitionBand3964)) (transitionJoin (transitionFromBand transitionBand3988) (transitionFromBand transitionBand4012)))
end Finite4848.Audit.Simple.Compact

namespace Finite4848.Audit.Simple.Compact
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand0 : cutBand 10 0 1=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
theorem cutLayer0 : CutRange 10 0 1 :=
  (cutFromBand cutBand0)
end Finite4848.Audit.Simple.Compact

namespace Finite4848.Audit.Simple.Compact
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1 : cutBand 9 1 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand25 : cutBand 9 25 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand49 : cutBand 9 49 17=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
theorem cutLayer1 : CutRange 9 1 66 :=
  (cutJoin (cutFromBand cutBand1) (cutJoin (cutFromBand cutBand25) (cutFromBand cutBand49)))
end Finite4848.Audit.Simple.Compact

namespace Finite4848.Audit.Simple.Compact
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand66 : cutBand 8 66 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand90 : cutBand 8 90 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand114 : cutBand 8 114 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand138 : cutBand 8 138 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand162 : cutBand 8 162 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand186 : cutBand 8 186 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand210 : cutBand 8 210 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand234 : cutBand 8 234 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand258 : cutBand 8 258 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand282 : cutBand 8 282 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand306 : cutBand 8 306 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand330 : cutBand 8 330 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand354 : cutBand 8 354 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand378 : cutBand 8 378 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand402 : cutBand 8 402 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand426 : cutBand 8 426 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand450 : cutBand 8 450 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand474 : cutBand 8 474 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand498 : cutBand 8 498 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand522 : cutBand 8 522 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand546 : cutBand 8 546 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand570 : cutBand 8 570 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand594 : cutBand 8 594 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand618 : cutBand 8 618 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand642 : cutBand 8 642 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand666 : cutBand 8 666 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand690 : cutBand 8 690 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand714 : cutBand 8 714 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand738 : cutBand 8 738 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand762 : cutBand 8 762 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand786 : cutBand 8 786 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand810 : cutBand 8 810 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand834 : cutBand 8 834 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand858 : cutBand 8 858 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand882 : cutBand 8 882 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand906 : cutBand 8 906 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand930 : cutBand 8 930 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand954 : cutBand 8 954 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand978 : cutBand 8 978 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1002 : cutBand 8 1002 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1026 : cutBand 8 1026 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1050 : cutBand 8 1050 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1074 : cutBand 8 1074 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1098 : cutBand 8 1098 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1122 : cutBand 8 1122 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1146 : cutBand 8 1146 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1170 : cutBand 8 1170 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1194 : cutBand 8 1194 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1218 : cutBand 8 1218 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1242 : cutBand 8 1242 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1266 : cutBand 8 1266 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1290 : cutBand 8 1290 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1314 : cutBand 8 1314 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1338 : cutBand 8 1338 12=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
theorem cutLayer2 : CutRange 8 66 1350 :=
  (cutJoin (cutJoin (cutJoin (cutJoin (cutJoin (cutFromBand cutBand66) (cutJoin (cutFromBand cutBand90) (cutFromBand cutBand114))) (cutJoin (cutFromBand cutBand138) (cutJoin (cutFromBand cutBand162) (cutFromBand cutBand186)))) (cutJoin (cutJoin (cutFromBand cutBand210) (cutJoin (cutFromBand cutBand234) (cutFromBand cutBand258))) (cutJoin (cutJoin (cutFromBand cutBand282) (cutFromBand cutBand306)) (cutJoin (cutFromBand cutBand330) (cutFromBand cutBand354))))) (cutJoin (cutJoin (cutJoin (cutFromBand cutBand378) (cutJoin (cutFromBand cutBand402) (cutFromBand cutBand426))) (cutJoin (cutJoin (cutFromBand cutBand450) (cutFromBand cutBand474)) (cutJoin (cutFromBand cutBand498) (cutFromBand cutBand522)))) (cutJoin (cutJoin (cutFromBand cutBand546) (cutJoin (cutFromBand cutBand570) (cutFromBand cutBand594))) (cutJoin (cutJoin (cutFromBand cutBand618) (cutFromBand cutBand642)) (cutJoin (cutFromBand cutBand666) (cutFromBand cutBand690)))))) (cutJoin (cutJoin (cutJoin (cutJoin (cutFromBand cutBand714) (cutJoin (cutFromBand cutBand738) (cutFromBand cutBand762))) (cutJoin (cutFromBand cutBand786) (cutJoin (cutFromBand cutBand810) (cutFromBand cutBand834)))) (cutJoin (cutJoin (cutFromBand cutBand858) (cutJoin (cutFromBand cutBand882) (cutFromBand cutBand906))) (cutJoin (cutJoin (cutFromBand cutBand930) (cutFromBand cutBand954)) (cutJoin (cutFromBand cutBand978) (cutFromBand cutBand1002))))) (cutJoin (cutJoin (cutJoin (cutFromBand cutBand1026) (cutJoin (cutFromBand cutBand1050) (cutFromBand cutBand1074))) (cutJoin (cutJoin (cutFromBand cutBand1098) (cutFromBand cutBand1122)) (cutJoin (cutFromBand cutBand1146) (cutFromBand cutBand1170)))) (cutJoin (cutJoin (cutFromBand cutBand1194) (cutJoin (cutFromBand cutBand1218) (cutFromBand cutBand1242))) (cutJoin (cutJoin (cutFromBand cutBand1266) (cutFromBand cutBand1290)) (cutJoin (cutFromBand cutBand1314) (cutFromBand cutBand1338)))))))
end Finite4848.Audit.Simple.Compact

namespace Finite4848.Audit.Simple.Compact
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1350 : cutBand 7 1350 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1374 : cutBand 7 1374 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1398 : cutBand 7 1398 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1422 : cutBand 7 1422 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1446 : cutBand 7 1446 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1470 : cutBand 7 1470 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1494 : cutBand 7 1494 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1518 : cutBand 7 1518 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1542 : cutBand 7 1542 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1566 : cutBand 7 1566 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1590 : cutBand 7 1590 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1614 : cutBand 7 1614 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1638 : cutBand 7 1638 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1662 : cutBand 7 1662 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1686 : cutBand 7 1686 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1710 : cutBand 7 1710 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1734 : cutBand 7 1734 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1758 : cutBand 7 1758 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1782 : cutBand 7 1782 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1806 : cutBand 7 1806 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1830 : cutBand 7 1830 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1854 : cutBand 7 1854 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1878 : cutBand 7 1878 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1902 : cutBand 7 1902 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1926 : cutBand 7 1926 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1950 : cutBand 7 1950 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1974 : cutBand 7 1974 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand1998 : cutBand 7 1998 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2022 : cutBand 7 2022 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2046 : cutBand 7 2046 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2070 : cutBand 7 2070 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2094 : cutBand 7 2094 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2118 : cutBand 7 2118 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2142 : cutBand 7 2142 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2166 : cutBand 7 2166 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2190 : cutBand 7 2190 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2214 : cutBand 7 2214 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2238 : cutBand 7 2238 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2262 : cutBand 7 2262 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2286 : cutBand 7 2286 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2310 : cutBand 7 2310 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2334 : cutBand 7 2334 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2358 : cutBand 7 2358 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2382 : cutBand 7 2382 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2406 : cutBand 7 2406 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2430 : cutBand 7 2430 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2454 : cutBand 7 2454 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2478 : cutBand 7 2478 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2502 : cutBand 7 2502 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2526 : cutBand 7 2526 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2550 : cutBand 7 2550 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2574 : cutBand 7 2574 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2598 : cutBand 7 2598 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2622 : cutBand 7 2622 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2646 : cutBand 7 2646 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2670 : cutBand 7 2670 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2694 : cutBand 7 2694 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2718 : cutBand 7 2718 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2742 : cutBand 7 2742 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2766 : cutBand 7 2766 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2790 : cutBand 7 2790 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2814 : cutBand 7 2814 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2838 : cutBand 7 2838 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2862 : cutBand 7 2862 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2886 : cutBand 7 2886 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2910 : cutBand 7 2910 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2934 : cutBand 7 2934 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2958 : cutBand 7 2958 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand2982 : cutBand 7 2982 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3006 : cutBand 7 3006 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3030 : cutBand 7 3030 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3054 : cutBand 7 3054 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3078 : cutBand 7 3078 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3102 : cutBand 7 3102 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3126 : cutBand 7 3126 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3150 : cutBand 7 3150 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3174 : cutBand 7 3174 15=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
theorem cutLayer3 : CutRange 7 1350 3189 :=
  (cutJoin (cutJoin (cutJoin (cutJoin (cutJoin (cutJoin (cutFromBand cutBand1350) (cutFromBand cutBand1374)) (cutJoin (cutFromBand cutBand1398) (cutFromBand cutBand1422))) (cutJoin (cutJoin (cutFromBand cutBand1446) (cutFromBand cutBand1470)) (cutJoin (cutFromBand cutBand1494) (cutJoin (cutFromBand cutBand1518) (cutFromBand cutBand1542))))) (cutJoin (cutJoin (cutJoin (cutFromBand cutBand1566) (cutFromBand cutBand1590)) (cutJoin (cutFromBand cutBand1614) (cutJoin (cutFromBand cutBand1638) (cutFromBand cutBand1662)))) (cutJoin (cutJoin (cutFromBand cutBand1686) (cutFromBand cutBand1710)) (cutJoin (cutFromBand cutBand1734) (cutJoin (cutFromBand cutBand1758) (cutFromBand cutBand1782)))))) (cutJoin (cutJoin (cutJoin (cutJoin (cutFromBand cutBand1806) (cutFromBand cutBand1830)) (cutJoin (cutFromBand cutBand1854) (cutFromBand cutBand1878))) (cutJoin (cutJoin (cutFromBand cutBand1902) (cutFromBand cutBand1926)) (cutJoin (cutFromBand cutBand1950) (cutJoin (cutFromBand cutBand1974) (cutFromBand cutBand1998))))) (cutJoin (cutJoin (cutJoin (cutFromBand cutBand2022) (cutFromBand cutBand2046)) (cutJoin (cutFromBand cutBand2070) (cutJoin (cutFromBand cutBand2094) (cutFromBand cutBand2118)))) (cutJoin (cutJoin (cutFromBand cutBand2142) (cutFromBand cutBand2166)) (cutJoin (cutFromBand cutBand2190) (cutJoin (cutFromBand cutBand2214) (cutFromBand cutBand2238))))))) (cutJoin (cutJoin (cutJoin (cutJoin (cutJoin (cutFromBand cutBand2262) (cutFromBand cutBand2286)) (cutJoin (cutFromBand cutBand2310) (cutFromBand cutBand2334))) (cutJoin (cutJoin (cutFromBand cutBand2358) (cutFromBand cutBand2382)) (cutJoin (cutFromBand cutBand2406) (cutJoin (cutFromBand cutBand2430) (cutFromBand cutBand2454))))) (cutJoin (cutJoin (cutJoin (cutFromBand cutBand2478) (cutFromBand cutBand2502)) (cutJoin (cutFromBand cutBand2526) (cutJoin (cutFromBand cutBand2550) (cutFromBand cutBand2574)))) (cutJoin (cutJoin (cutFromBand cutBand2598) (cutFromBand cutBand2622)) (cutJoin (cutFromBand cutBand2646) (cutJoin (cutFromBand cutBand2670) (cutFromBand cutBand2694)))))) (cutJoin (cutJoin (cutJoin (cutJoin (cutFromBand cutBand2718) (cutFromBand cutBand2742)) (cutJoin (cutFromBand cutBand2766) (cutJoin (cutFromBand cutBand2790) (cutFromBand cutBand2814)))) (cutJoin (cutJoin (cutFromBand cutBand2838) (cutFromBand cutBand2862)) (cutJoin (cutFromBand cutBand2886) (cutJoin (cutFromBand cutBand2910) (cutFromBand cutBand2934))))) (cutJoin (cutJoin (cutJoin (cutFromBand cutBand2958) (cutFromBand cutBand2982)) (cutJoin (cutFromBand cutBand3006) (cutJoin (cutFromBand cutBand3030) (cutFromBand cutBand3054)))) (cutJoin (cutJoin (cutFromBand cutBand3078) (cutFromBand cutBand3102)) (cutJoin (cutFromBand cutBand3126) (cutJoin (cutFromBand cutBand3150) (cutFromBand cutBand3174))))))))
end Finite4848.Audit.Simple.Compact

namespace Finite4848.Audit.Simple.Compact
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3189 : cutBand 6 3189 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3213 : cutBand 6 3213 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3237 : cutBand 6 3237 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3261 : cutBand 6 3261 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3285 : cutBand 6 3285 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3309 : cutBand 6 3309 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3333 : cutBand 6 3333 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3357 : cutBand 6 3357 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3381 : cutBand 6 3381 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3405 : cutBand 6 3405 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3429 : cutBand 6 3429 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3453 : cutBand 6 3453 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3477 : cutBand 6 3477 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3501 : cutBand 6 3501 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3525 : cutBand 6 3525 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3549 : cutBand 6 3549 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3573 : cutBand 6 3573 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3597 : cutBand 6 3597 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3621 : cutBand 6 3621 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3645 : cutBand 6 3645 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3669 : cutBand 6 3669 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3693 : cutBand 6 3693 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3717 : cutBand 6 3717 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3741 : cutBand 6 3741 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3765 : cutBand 6 3765 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3789 : cutBand 6 3789 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3813 : cutBand 6 3813 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3837 : cutBand 6 3837 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3861 : cutBand 6 3861 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3885 : cutBand 6 3885 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3909 : cutBand 6 3909 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3933 : cutBand 6 3933 7=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
theorem cutLayer4 : CutRange 6 3189 3940 :=
  (cutJoin (cutJoin (cutJoin (cutJoin (cutJoin (cutFromBand cutBand3189) (cutFromBand cutBand3213)) (cutJoin (cutFromBand cutBand3237) (cutFromBand cutBand3261))) (cutJoin (cutJoin (cutFromBand cutBand3285) (cutFromBand cutBand3309)) (cutJoin (cutFromBand cutBand3333) (cutFromBand cutBand3357)))) (cutJoin (cutJoin (cutJoin (cutFromBand cutBand3381) (cutFromBand cutBand3405)) (cutJoin (cutFromBand cutBand3429) (cutFromBand cutBand3453))) (cutJoin (cutJoin (cutFromBand cutBand3477) (cutFromBand cutBand3501)) (cutJoin (cutFromBand cutBand3525) (cutFromBand cutBand3549))))) (cutJoin (cutJoin (cutJoin (cutJoin (cutFromBand cutBand3573) (cutFromBand cutBand3597)) (cutJoin (cutFromBand cutBand3621) (cutFromBand cutBand3645))) (cutJoin (cutJoin (cutFromBand cutBand3669) (cutFromBand cutBand3693)) (cutJoin (cutFromBand cutBand3717) (cutFromBand cutBand3741)))) (cutJoin (cutJoin (cutJoin (cutFromBand cutBand3765) (cutFromBand cutBand3789)) (cutJoin (cutFromBand cutBand3813) (cutFromBand cutBand3837))) (cutJoin (cutJoin (cutFromBand cutBand3861) (cutFromBand cutBand3885)) (cutJoin (cutFromBand cutBand3909) (cutFromBand cutBand3933))))))
end Finite4848.Audit.Simple.Compact

namespace Finite4848.Audit.Simple.Compact
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3940 : cutBand 5 3940 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3964 : cutBand 5 3964 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand3988 : cutBand 5 3988 24=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem cutBand4012 : cutBand 5 4012 10=true := MaskCut.convertBand MaskCut.labelsVerified MaskCut.sortedVerified (by decide +kernel)
theorem cutLayer5 : CutRange 5 3940 4022 :=
  (cutJoin (cutJoin (cutFromBand cutBand3940) (cutFromBand cutBand3964)) (cutJoin (cutFromBand cutBand3988) (cutFromBand cutBand4012)))
end Finite4848.Audit.Simple.Compact

namespace Finite4848.Audit.Simple.Compact

theorem finished : search 10 basis=false :=
  compact_conclude transitionLayer5 cutLayer5 transitionLayer4 cutLayer4
    transitionLayer3 cutLayer3 transitionLayer2 cutLayer2
    transitionLayer1 cutLayer1 transitionLayer0 cutLayer0

end Finite4848.Audit.Simple.Compact

end PEqualNP.Outside.L_meta_4849

theorem PEqualNP.Outside.L_meta_4849 : ¬ (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → PEqualNP.TopForm.NoFourCycle x2 → ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x6 → PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → ∀ x9 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x12 x13 : Fin x1), PEqualNP.EdgeOwnership.gateVal x1 x6 x9 (PEqualNP.EdgeOwnership.pairInput x12 x13) = Bool.true → x2.Adj x12 x13) := by
  apply PEqualNP.Outside.L_meta_4849.Refute4848.exact_negation
  exact PEqualNP.Outside.L_meta_4849.Refute4848.Root.minimum_of_search
    PEqualNP.Outside.L_meta_4849.Finite4848.Audit.Simple.Compact.finished
