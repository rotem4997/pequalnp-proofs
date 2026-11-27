import Mathlib
import PEqualNP.Defs

-- Wire bookkeeping and girth lemmas adapted from the accepted proof L-meta-4115.
namespace PEqualNP.Outside.L_meta_9004

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def pins (g : Gate) := g.inputs.take (bif g.op.eval [false] then 1 else 2)
def mark {n : Nat} (S : Finset (Fin n)) (v : Fin n) := decide (v ∈ S)
def atBank (g : Gate) (z : List Bool) := g.op.eval (g.inputs.map fun k => z.getD k false)

lemma raw {n} (x : Fin n → Bool) (tail : List Bool) (i : Fin n) :
    (List.ofFn x ++ tail).getD i.val false = x i := by
  simp [List.getD_eq_getElem?_getD,List.getElem?_append,i.isLt]

lemma same_pin {n} (x y : Fin n → Bool) (tail : List Bool) (i : Nat)
    (h : ∀ j : Fin n, i=j.val → x j=y j) :
    (List.ofFn x ++ tail).getD i false = (List.ofFn y ++ tail).getD i false := by
  by_cases b : i<n
  · let j : Fin n := ⟨i,b⟩
    exact (raw x tail j).trans ((h j rfl).trans (raw y tail j).symm)
  · simp [List.getD_eq_getElem?_getD,List.getElem?_append,b]

lemma eval_from_pins (g : Gate) (z w : List Bool)
    (fan : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (agree : ∀ i ∈ pins g, z.getD i false = w.getD i false) : atBank g z = atBank g w := by
  obtain ⟨op,ins⟩ := g
  rcases fan with ⟨opok,arity⟩
  change op = .and ∨ op = .or ∨ op = .not at opok
  change ins.length ≤ 2 at arity
  rcases opok with rfl|rfl|rfl <;> cases ins with
  | nil => rfl
  | cons a tail =>
    cases tail with
    | nil =>
      have ha := agree a (by simp [pins,GateOp.eval])
      simp [atBank,GateOp.eval,List.getD_eq_getElem?_getD] at ha ⊢ <;> simp [ha]
    | cons b t =>
      have empty : t=[] := by simpa using arity
      subst t
      have ha := agree a (by simp [pins,GateOp.eval])
      simp [atBank,GateOp.eval,List.getD_eq_getElem?_getD] at ha ⊢
      rw [ha]
      all_goals
        have hb := agree b (by simp [pins,GateOp.eval])
        simp only [List.getD_eq_getElem?_getD] at hb
        rw [hb]

lemma parallel_wires {n} (x y : Fin n → Bool) (gs : List Gate)
    (step : ∀ g ∈ gs, ∀ rest, atBank g (List.ofFn x ++ rest) = atBank g (List.ofFn y ++ rest))
    (t : List Bool) : ∃ suffix, (Circuit.mk gs 0).wires (List.ofFn x ++ t) = List.ofFn x ++ suffix ∧
      (Circuit.mk gs 0).wires (List.ofFn y ++ t) = List.ofFn y ++ suffix := by
  induction gs generalizing t with
  | nil => exact ⟨t,rfl,rfl⟩
  | cons g gs ih =>
    have eq := step g (by simp) t
    obtain ⟨s,hx,hy⟩ := ih (fun a ha => step a (List.mem_cons_of_mem _ ha)) (t++[atBank g (List.ofFn x ++ t)])
    refine ⟨s,?_,?_⟩
    · change (Circuit.mk gs 0).wires ((List.ofFn x ++ t) ++ [atBank g _]) = _
      simpa only [List.append_assoc] using hx
    · change (Circuit.mk gs 0).wires ((List.ofFn y ++ t) ++ [atBank g _]) = _
      rw [←eq]
      simpa only [List.append_assoc] using hy

lemma lockstep_all {n} (C : Circuit) (x y : Fin n → Bool)
    (out : n ≤ C.output)
    (step : ∀ q ∈ C.gates, ∀ tail, atBank q (List.ofFn x ++ tail) = atBank q (List.ofFn y ++ tail)) :
    C.eval (List.ofFn x) = C.eval (List.ofFn y) := by
  obtain ⟨s,hx,hy⟩ := parallel_wires x y _ step []
  simp only [List.append_nil] at hx hy
  change ((Circuit.mk C.gates 0).wires (List.ofFn x)).getD _ false =
    ((Circuit.mk C.gates 0).wires (List.ofFn y)).getD _ false
  rw [hx,hy]
  exact same_pin x y s C.output (fun j h => by have := j.isLt; omega)

section Geometry
open SimpleGraph
variable {n : ℕ} {G : SimpleGraph (Fin n)}
def girthFive (G : SimpleGraph (Fin n)) := ∀ u (p : G.Walk u u), p.IsCycle → 5 ≤ p.length

lemma triangle (h : girthFive G) {u v w : Fin n} (uv : G.Adj u v) (vw : G.Adj v w)
    (wu : G.Adj w u) : False := by
  let p := Walk.cons uv (Walk.cons vw (Walk.cons wu Walk.nil))
  have hp : p.IsCycle := by
    unfold p
    rw [Walk.cons_isCycle_iff]
    have a := uv.ne
    have b := vw.ne
    have c := wu.ne
    constructor <;> simp [Walk.cons_isPath_iff,Sym2.eq_iff,a,b,c,Ne.symm a,Ne.symm b,Ne.symm c]
  have bound := h u p hp
  simp [p] at bound

lemma square (h : girthFive G) {u a w b : Fin n} (ua : G.Adj u a) (aw : G.Adj a w)
    (wb : G.Adj w b) (bu : G.Adj b u) (uw : u ≠ w) (ab : a ≠ b) : False := by
  let p := Walk.cons ua (Walk.cons aw (Walk.cons wb (Walk.cons bu Walk.nil)))
  have hp : p.IsCycle := by
    unfold p
    rw [Walk.cons_isCycle_iff]
    have h1 := ua.ne
    have h2 := aw.ne
    have h3 := wb.ne
    have h4 := bu.ne
    constructor <;> simp [Walk.cons_isPath_iff,Sym2.eq_iff,h1,h2,h3,h4,uw,ab,
      Ne.symm h1,Ne.symm h2,Ne.symm h3,Ne.symm h4,Ne.symm uw,Ne.symm ab]
  have bound := h u p hp
  simp [p] at bound

-- a vertex `w` other than `u` touches at most one neighbour of `u`
lemma kill_once (h : girthFive G) {u w r s : Fin n} (uw : u ≠ w)
    (ur : G.Adj u r) (us : G.Adj u s) (rs : r ≠ s)
    (kr : r = w ∨ G.Adj w r) (ks : s = w ∨ G.Adj w s) : False := by
  rcases kr with rfl|kr <;> rcases ks with rfl|ks
  · exact rs rfl
  · exact triangle h ur ks us.symm
  · exact triangle h us kr ur.symm
  · exact square h ur kr.symm ks us.symm uw rs

lemma free_neighbor (h : girthFive G) {u w1 w2 a b c : Fin n} (u1 : u ≠ w1) (u2 : u ≠ w2)
    (ua : G.Adj u a) (ub : G.Adj u b) (uc : G.Adj u c) (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) :
    ∃ r, G.Adj u r ∧ r ≠ w1 ∧ ¬ G.Adj w1 r ∧ r ≠ w2 ∧ ¬ G.Adj w2 r := by
  have k1ab := kill_once h u1 ua ub ab
  have k1ac := kill_once h u1 ua uc ac
  have k1bc := kill_once h u1 ub uc bc
  have k2ab := kill_once h u2 ua ub ab
  have k2ac := kill_once h u2 ua uc ac
  have k2bc := kill_once h u2 ub uc bc
  by_cases pa : (a = w1 ∨ G.Adj w1 a) ∨ (a = w2 ∨ G.Adj w2 a)
  · by_cases pb : (b = w1 ∨ G.Adj w1 b) ∨ (b = w2 ∨ G.Adj w2 b)
    · have h1 : ¬ (c = w1 ∨ G.Adj w1 c) := fun hc => by
        rcases pa with pa|pa
        · exact k1ac pa hc
        rcases pb with pb|pb
        · exact k1bc pb hc
        exact k2ab pa pb
      have h2 : ¬ (c = w2 ∨ G.Adj w2 c) := fun hc => by
        rcases pa with pa|pa
        · rcases pb with pb|pb
          · exact k1ab pa pb
          · exact k2bc pb hc
        exact k2ac pa hc
      exact ⟨c, uc, fun e => h1 (Or.inl e), fun e => h1 (Or.inr e), fun e => h2 (Or.inl e),
        fun e => h2 (Or.inr e)⟩
    · exact ⟨b, ub, fun e => pb (Or.inl (Or.inl e)), fun e => pb (Or.inl (Or.inr e)),
        fun e => pb (Or.inr (Or.inl e)), fun e => pb (Or.inr (Or.inr e))⟩
  · exact ⟨a, ua, fun e => pa (Or.inl (Or.inl e)), fun e => pa (Or.inl (Or.inr e)),
      fun e => pa (Or.inr (Or.inl e)), fun e => pa (Or.inr (Or.inr e))⟩
end Geometry

open SimpleGraph
variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n))

lemma mark_true (S : Finset (Fin n)) :
    graphFun G A (mark S) = true ↔
      (∃ i ∈ A, i ∈ S) ∨ (∃ i j, G.Adj i j ∧ i ∈ S ∧ j ∈ S) := by
  simp [graphFun,mark]

lemma off_triple (a b c : Fin n) (ao : a ∉ A) (bo : b ∉ A) (co : c ∉ A) (ab : ¬G.Adj a b)
    (ac : ¬G.Adj a c) (bc : ¬G.Adj b c) :
    graphFun G A (mark {a,b,c}) = false := by
  apply Bool.eq_false_iff.mpr
  intro yes
  rcases (mark_true G A _).mp yes with ⟨i,hi,mem⟩|⟨i,j,adj,hi,hj⟩
  · simp only [Finset.mem_insert,Finset.mem_singleton] at mem
    rcases mem with rfl|rfl|rfl
    · exact ao hi
    · exact bo hi
    · exact co hi
  · simp only [Finset.mem_insert,Finset.mem_singleton] at hi hj
    rcases hi with rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl <;>
      first | exact adj.ne rfl | exact absurd adj (by assumption) | exact absurd adj.symm (by assumption)

lemma off_one (a : Fin n) (ao : a ∉ A) : graphFun G A (mark {a}) = false := by
  have := off_triple G A a a a ao ao ao (G.loopless.irrefl a) (G.loopless.irrefl a)
    (G.loopless.irrefl a)
  simpa using this

lemma on_edge {a b : Fin n} (ab : G.Adj a b) (S : Finset (Fin n)) (aS : a∈S) (bS : b∈S) :
    graphFun G A (mark S) = true :=
  (mark_true G A S).mpr (Or.inr ⟨a,b,ab,aS,bS⟩)

lemma not_raw_output (C : Circuit) (out : circuitFun n C = graphFun G A)
    (apart : ∀ i j, G.Adj i j → i ∉ A) (edge : ∃ i j, G.Adj i j) :
    n ≤ C.output := by
  by_contra! small
  let k : Fin n := ⟨C.output,small⟩
  have projected (x : Fin n → Bool) : graphFun G A x = x k := by
    rw [←out]
    change ((wiresFrom C.gates (List.ofFn x)).getD k.val false) = _
    rw [getD_wiresFrom _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD]
  by_cases hk : k ∈ A
  · obtain ⟨a,b,adj⟩ := edge
    have ak : k ≠ a := fun e => apart a b adj (e ▸ hk)
    have bk : k ≠ b := fun e => apart b a adj.symm (e ▸ hk)
    have yes := on_edge G A adj {a,b} (by simp) (by simp)
    rw [projected] at yes
    simp [mark,ak,bk] at yes
  · have no := off_one G A k hk
    rw [projected] at no
    simp [mark] at no

lemma three_neighbors (u : Fin n) (degree : (G.neighborSet u).ncard = 3) :
    ∃ a b c, G.Adj u a ∧ G.Adj u b ∧ G.Adj u c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  have card : (G.neighborFinset u).card = 3 := by
    change (G.neighborSet u).toFinset.card = 3
    rw [← Set.ncard_eq_toFinset_card']
    exact degree
  obtain ⟨a,b,c,ab,ac,bc,hs⟩ := Finset.card_eq_three.mp card
  have ha : a ∈ G.neighborFinset u := by rw [hs]; simp
  have hb : b ∈ G.neighborFinset u := by rw [hs]; simp
  have hc : c ∈ G.neighborFinset u := by rw [hs]; simp
  exact ⟨a,b,c,(G.mem_neighborFinset _ _).mp ha,(G.mem_neighborFinset _ _).mp hb,
    (G.mem_neighborFinset _ _).mp hc,ab,ac,bc⟩

lemma or_pair (u v : Fin n) (g : Gate) (ord : g.inputs.Perm [u.val,v.val])
    (op : g.op = .or) (x : Fin n → Bool) (t : List Bool) :
    atBank g (List.ofFn x ++ t) = (x u || x v) := by
  rcases List.perm_pair.mp ord with e|e <;>
    simp only [atBank,e,op,List.map_cons,List.map_nil,raw,GateOp.eval] <;>
    simp [Bool.or_comm]

lemma main (C : Circuit) (u v w : Fin n)
    (degree : (G.neighborSet u).ncard = 3)
    (girth : ∀ i (p : G.Walk i i), p.IsCycle → 7 ≤ p.length)
    (apart : ∀ i j, G.Adj i j → i ∉ A) (uo : u ∉ A) (vo : v ∉ A) (wo : w ∉ A)
    (uv : u ≠ v) (uw : u ≠ w) (fan : FanInTwo C) (correct : circuitFun n C = graphFun G A)
    (readers : ∀ q ∈ C.gates, u.val ∈ pins q →
      q.op = GateOp.or ∧ (q.inputs.Perm [u.val, v.val] ∨ q.inputs.Perm [u.val, w.val])) :
    G.Adj v w := by
  by_contra vw
  obtain ⟨a,b,c,ua,ub,uc,ab,ac,bc⟩ := three_neighbors G u degree
  have short : girthFive G := fun i p hp => le_trans (by decide : 5 ≤ 7) (girth i p hp)
  have out := not_raw_output G A C correct apart ⟨u,a,ua⟩
  obtain ⟨r,ur,rv,vr,rw,wr⟩ := free_neighbor short uv uw ua ub uc ab ac bc
  have ro : r ∉ A := apart _ _ ur.symm
  have ru : r ≠ u := ur.ne.symm
  have step : ∀ q ∈ C.gates, ∀ tail, atBank q (List.ofFn (mark {v,w,r}) ++ tail)
      = atBank q (List.ofFn (mark (insert u {v,w,r})) ++ tail) := by
    intro q hq tail
    by_cases hu : u.val ∈ pins q
    · obtain ⟨op, hp⟩ := readers q hq hu
      rcases hp with hp|hp
      · rw [or_pair u v q hp op, or_pair u v q hp op]
        simp [mark]
      · rw [or_pair u w q hp op, or_pair u w q hp op]
        simp [mark]
    · apply eval_from_pins _ _ _ (fan q hq)
      intro i hi
      apply same_pin
      rintro j rfl
      have ju : j ≠ u := by rintro rfl; exact hu hi
      simp [mark, ju]
  have eq := lockstep_all C _ _ out step
  change circuitFun n C _ = circuitFun n C _ at eq
  rw [correct, off_triple G A v w r vo wo ro vw (fun e => vr e) (fun e => wr e),
    on_edge G A ur _ (by simp) (by simp)] at eq
  exact Bool.false_ne_true eq

end PEqualNP.Outside.L_meta_9004

theorem PEqualNP.Outside.L_meta_9004 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 x8 : Fin x1), (x2.neighborSet x6).ncard = (3 : ℕ) → (∀ (x10 : Fin x1) (x11 : x2.Walk x10 x10), x11.IsCycle → (7 : ℕ) ≤ x11.length) → (∀ (x11 x12 : Fin x1), x2.Adj x11 x12 → x11 ∉ x4) → x6 ∉ x4 → x7 ∉ x4 → x8 ∉ x4 → x6 ≠ x7 → x6 ≠ x8 → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 → (∀ x19 ∈ x5.gates, ↑x6 ∈ List.take (bif x19.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x19.inputs → x19.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (x19.inputs.Perm [↑x6, ↑x7] ∨ x19.inputs.Perm [↑x6, ↑x8])) → x2.Adj x7 x8 := by
  intro n G dec A C u v w degree girth apart uo vo wo uv uw fan correct readers
  exact PEqualNP.Outside.L_meta_9004.main G A C u v w degree girth apart uo vo wo uv uw fan
    correct readers
